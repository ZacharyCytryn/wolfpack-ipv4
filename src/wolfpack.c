#include <ctype.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <math.h>
#include <assert.h>

#include "wolfpack.h"

void print_packet_sf(const unsigned char *packet) {

    // Loops for header
    for (int i = 0; i < 24; i++) {
        if (i == 5 || i == 10 || i == 11 || i == 12 || i == 15 || i == 17 || i == 20) {
            printf("\n");
        }
        printf("%02x", packet[i]);
    }
    printf("\n");

    unsigned int packet_length = (packet[17] << 16) + (packet[18] << 8) + packet[19];
    //Loop for payload
    for (int i = 24; i < packet_length; i++) {
        printf("%c", packet[i]);
    }
    printf("\n");

}

unsigned int packetize_sf(const char *message, unsigned char *packets[], unsigned int packets_len, unsigned int max_payload,
    unsigned long src_addr, unsigned long dest_addr, unsigned short flags) {

    unsigned packets_created = 0;
    int bytes_required = 0;
    int bytes_left = strlen(message);
    unsigned int packet_length = 24;
    int shifter = 0;
    int byte_remainder = max_payload;
    unsigned long addr_holder = src_addr;
    for (int i = 0; i < packets_len; i++) {
        packet_length = 24;
        if (bytes_left > max_payload) {
            packet_length += max_payload;
            packets[i] = malloc(packet_length);
            bytes_left -= max_payload;
            packets_created++;
        }
        else {
            if (bytes_left != 0) {
                byte_remainder = bytes_left;
                packet_length += bytes_left;
                packets[i] = malloc(packet_length);
                packets_created++;
                bytes_left = 0;
            }
            else {
                break;
            }
        }
        shifter = 16;
        for (int j = 17; j < 20; j++) {
            packets[i][j] = packet_length >> shifter;
            if (shifter != 0) {
                packet_length &= ~(0xFF << (shifter - 2));
            }
            shifter -= 8;
        }
    }

    unsigned int fragment = 0;
    unsigned short temp_flags = flags;
    unsigned int checksum = 0;
    int message_index = 0;
    for (int i = 0; i < packets_created; i++) {
        addr_holder = src_addr;
        // Source address
        shifter = 32;
        packets[i][0] = addr_holder >> shifter;
        shifter -= 8;
        addr_holder &= ~(0xFF00000000);
        for (int j = 1; j < 5; j++) {
            packets[i][j] = (addr_holder >> shifter);
            if (shifter != 0) {
                addr_holder &= ~(0xFF << (shifter));
            }
            shifter -= 8;
        }
        // Destination address
        addr_holder = dest_addr;
        shifter = 32;
        packets[i][5] = addr_holder >> shifter;
        shifter -= 8;
        for (int j = 6; j < 10; j++) {
            packets[i][j] = (addr_holder >> shifter);
            if (shifter != 0) {
                addr_holder &= ~(0xFF << (shifter));
            }
            shifter -= 8;
        }

        // Source and destination ports
        packets[i][10] = 0x20;
        packets[i][11] = 0x40;

        // Fragment offset
        fragment = max_payload * i;
        message_index = fragment;
        shifter = 16;
        for (int j = 12; j < 15; j++) {
            packets[i][j] = (fragment >> shifter);
            if (shifter != 0) {
                fragment &= ~(0xFF << (shifter));
            }
            shifter -= 8;
        }

        // Flags
        shifter = 8;
        temp_flags = flags;
        for (int j = 15; j < 17; j++) {
            packets[i][j] = (temp_flags >> shifter);
            if (shifter != 0) {
                temp_flags &= ~(0xFF << (shifter));
            }
            shifter -= 8;
        }

        // Checksum (Packet length skipped; taken care of in first for-loop of function)
        shifter = 24;
        checksum = checksum_sf(packets[i]);
        for (int j = 20; j < 24; j++) {
            packets[i][j] = checksum >> shifter;
            if (shifter != 0) {
                checksum &= ~(0xFF << shifter);
            }
            shifter -= 8;
        }

        // Payload
        packet_length = (packets[i][17] << 16) + (packets[i][18] << 8) + packets[i][19];
        for (int j = 24; j < packet_length; j++) {
            packets[i][j] = message[message_index];
            message_index++;
        }
    }
    return packets_created;
}

unsigned int checksum_sf(const unsigned char *packet) {
    unsigned long long found_checksum = 0;
    unsigned int packet_length = (packet[17] << 16) + (packet[18] << 8) + packet[19];

    // Source address for-loop
    int shifter = 32;
    for (int i = 0; i < 5; i++) {
        found_checksum += (packet[i] << shifter);
        shifter -= 8;
    }
    // Destination address for-loop
    shifter = 32;
    for (int i = 5; i < 10; i++) {
        found_checksum += (packet[i] << shifter);
        shifter -= 8;
    }

    // Src port & Dst port added to checksum
    found_checksum += packet[10] + packet[11];

    // Fragment Offset for-loop
    shifter = 16;
    for (int i = 12; i < 15; i++) {
        found_checksum += (packet[i] << shifter);
        shifter -= 8;
    }

    // Flags for-loop
    shifter = 8;
    for (int i = 15; i < 17; i++) {
        found_checksum += (packet[i] << shifter);
        shifter -= 8;
    }

    // Total length for-loop
    shifter = 16;
    for (int i = 17; i < 20; i++) {
        found_checksum += (packet[i] << shifter);
        shifter -= 8;
    }

    //2^32 - 1 is 4294967295
    found_checksum %= 4294967295;
    if (packet[0] != '\x00' || packet[5] != '\x00') {
        return (unsigned int) found_checksum + 1;
    }
    else {
        return (unsigned int) found_checksum;
    }
}

unsigned int reconstruct_sf(unsigned char *packets[], unsigned int packets_len, char *message, unsigned int message_len) {
    unsigned int written_payloads = 0;
    unsigned int unchecked_sum = 0;
    unsigned int offset = 0;
    unsigned int length = 0;
    int message_index = 0; 
    int max_index = 0;
    for (int i = 0; i < packets_len; i++) {
        unchecked_sum = ((packets[i][20] << 24) + (packets[i][21] << 16) + (packets[i][22] << 8) + packets[i][23]);
        if (checksum_sf(packets[i]) == unchecked_sum) {
            offset = (packets[i][12] << 16) + (packets[i][13] << 8) + (packets[i][14]);
            if (offset < message_len) {
                written_payloads++;
                message_index = offset;
                length = (packets[i][17] << 16) + (packets[i][18] << 8) + packets[i][19];
                for (int j = 24; j < length; j++) {
                    if (message_index < message_len) {
                        message[message_index] = packets[i][j];
                        message_index++;
                        if (max_index < message_index && (message_index < message_len)) {
                            max_index = message_index;
                        }
                    }
                }
            }
        }
    }
    if (max_index != 0) {
        message[max_index] = 0;
    }
    return written_payloads;
}