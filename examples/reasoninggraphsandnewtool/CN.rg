( graph testfsm ( ( node N_2 delay_analysis ) 
( node N_1 model_checking ) 
( node N_4 and ) 
( node N_3 delay_analysis ) 
( node N_5 done ) ) 
( ( edge E_15 __ ( N_2 delayspec ) :type delay :encoding base64 :content QXV0b21hdGlvblJlcXVlc3RfaW5GIDogQXV0b21hdGlvblJlc3BvbnNlX291dEYgOiA5 ) 
( edge E_16 __ ( N_2 delaypath ) :type delay :encoding base64 :content Y29ubmVjdGlvbiA6IEF1dG9tYXRpb25SZXF1ZXN0X2luRiA6IEF1dG9tYXRpb25SZXF1ZXN0VmFsaWRhdG9yRi5DbWRSZXF1ZXN0X2luIDogMApmbG93IDogQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3JGIDogQ21kUmVxdWVzdF9pbiA6IFN1YlJlcXVlc3Rfb3V0IDogMQpjb25uZWN0aW9uIDogQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3JGLlN1YlJlcXVlc3Rfb3V0IDogUGxhbkJ1aWxkZXJGLkNtZFJlcXVlc3RfaW4gOiAwCmZsb3cgOiBQbGFuQnVpbGRlckYgOiBDbWRSZXF1ZXN0X2luIDogU3ViUmVxdWVzdF9vdXQgOiAxCmNvbm5lY3Rpb24gOiBQbGFuQnVpbGRlckYuU3ViUmVxdWVzdF9vdXQgOiBUYXNrU2VydmljZUJhc2VGLkNtZFJlcXVlc3RfaW4gOiAwCmZsb3cgOiBUYXNrU2VydmljZUJhc2VGIDogQ21kUmVxdWVzdF9pbiA6IFN1YlJlcXVlc3Rfb3V0IDogMQpjb25uZWN0aW9uIDogVGFza1NlcnZpY2VCYXNlRi5TdWJSZXF1ZXN0X291dCA6IFJvdXRlQWdncmVnYXRvckYuQ21kUmVxdWVzdF9pbiA6IDAKZmxvdyA6IFJvdXRlQWdncmVnYXRvckYgOiBDbWRSZXF1ZXN0X2luIDogU3ViUmVxdWVzdF9vdXQgOiAxCmNvbm5lY3Rpb24gOiBSb3V0ZUFnZ3JlZ2F0b3JGLlN1YlJlcXVlc3Rfb3V0IDogUGxhbm5lckYuQ21kUmVxdWVzdF9pbiA6IDAK ) 
( edge E_17 ( N_2 holds ) 
( N_4 in ) :type boolX :encoding base64 :content __ ) 
( edge E_18 ( N_2 explanation ) __ :type delay :encoding base64 :content __ ) 
( edge E_1 __ ( N_1 model ) :type nusmv :encoding base64 :content TU9EVUxFICJVeEFTUmVzcG9uZHNfcGtnRC5HZW5lcmljTGFzdFNlcnZpY2UiICggQ21kUmVxdWVzdF9pbiApDQpWQVIgcHJvY2Vzc2luZ19wYXRoIDogImltbC5wb3J0cy5GbG93UGF0aCIgIDsNClZBUiBDbWRSZXNwb25zZV9vdXQgOiAiaW1sLnBvcnRzLkV2ZW50RGF0YVBvcnQ8IGltbC5sYW5nLkJvb2wgPiIgIDsNClZBUiBnbW9uaXRvciA6ICJVeEFTUmVzcG9uZHNfcGtnRC5yZXNwb25kc19vbmNlIiAoQ21kUmVzcG9uc2Vfb3V0LmV2ZW50LENtZFJlcXVlc3RfaW4uZXZlbnQpIDsNClZBUiBkMSA6ICJpbWwucG9ydHMuZGVsYXkiIChwcm9jZXNzaW5nX3BhdGgsMSkgOw0KDQpERUZJTkUgZyA6PSAoIGdtb25pdG9yLmhvbGRzICAmICBkMS5ob2xkcyAgKSA7DQoNCklOVkFSICggKCAgcHJvY2Vzc2luZ19wYXRoLnN0YXJ0LmV2ZW50ID0gIENtZFJlcXVlc3RfaW4uZXZlbnQgICAmICAgcHJvY2Vzc2luZ19wYXRoLmVuZC5ldmVudCA9ICBDbWRSZXNwb25zZV9vdXQuZXZlbnQgICApICkgIDsNCg0KTU9EVUxFICJpbWwucG9ydHMuRmxvd1BvaW50IiANClZBUiB1cHBlckJvdW5kIDogImltbC5sYW5nLlJlYWwiICA7DQpWQVIgbG93ZXJCb3VuZCA6ICJpbWwubGFuZy5SZWFsIiAgOw0KVkFSIGV2ZW50IDogYm9vbGVhbiAgOw0KDQpNT0RVTEUgIlV4QVNSZXNwb25kc19wa2dELkdlbmVyaWNMYXN0U2VydmljZU5vRGVsYXkiICggQ21kUmVxdWVzdF9pbiApDQpWQVIgQ21kUmVzcG9uc2Vfb3V0IDogImltbC5wb3J0cy5FdmVudERhdGFQb3J0PCBpbWwubGFuZy5Cb29sID4iICA7DQpWQVIgZ21vbml0b3IgOiAiVXhBU1Jlc3BvbmRzX3BrZ0QucmVzcG9uZHNfb25jZSIgKENtZFJlc3BvbnNlX291dC5ldmVudCxDbWRSZXF1ZXN0X2luLmV2ZW50KSA7DQoNCkRFRklORSBnIDo9ICggZ21vbml0b3IuaG9sZHMgKSA7DQoNCk1PRFVMRSAiaW1sLnBvcnRzLmRlbGF5IiAoIGYsICBuICkNClZBUiBpIDogMC4uMjU2ICA7DQpWQVIgc3RhdGUgOiB7ImltbC5wb3J0cy5EZWxheVN0YXRlLnMwIiwiaW1sLnBvcnRzLkRlbGF5U3RhdGUuczEiLCJpbWwucG9ydHMuRGVsYXlTdGF0ZS5zMiJ9ICA7DQoNCkRFRklORSBzdGF0ZV9pX2luaXQgOj0gKCAgaSA9ICAxICApICAmICAoICBzdGF0ZSA9ICAiaW1sLnBvcnRzLkRlbGF5U3RhdGUuczAiICApICA7DQpJTklUIHN0YXRlX2lfaW5pdCA7DQoNCkRFRklORSBpX3RyYW5zIDo9ICggbmV4dChpKT0gIGNhc2UgDQoJc3RhdGU9ICAiaW1sLnBvcnRzLkRlbGF5U3RhdGUuczAiIDogMTsNCglzdGF0ZT0gICJpbWwucG9ydHMuRGVsYXlTdGF0ZS5zMSIgOiAgaSArIDE7DQoJVFJVRSA6IGk7DQplc2FjDQogKSA7DQpUUkFOUyBpX3RyYW5zIDsNCkRFRklORSBzX3RyYW5zIDo9ICggbmV4dChzdGF0ZSk9ICBjYXNlIA0KCXN0YXRlPSAgImltbC5wb3J0cy5EZWxheVN0YXRlLnMwIiAgJiAgZi5lbmQuZXZlbnQgIDogImltbC5wb3J0cy5EZWxheVN0YXRlLnMyIjsNCglzdGF0ZT0gICJpbWwucG9ydHMuRGVsYXlTdGF0ZS5zMCIgICYgIGYuc3RhcnQuZXZlbnQgIDogImltbC5wb3J0cy5EZWxheVN0YXRlLnMxIjsNCglzdGF0ZT0gICJpbWwucG9ydHMuRGVsYXlTdGF0ZS5zMSIgICYgIGYuZW5kLmV2ZW50ICA6ICJpbWwucG9ydHMuRGVsYXlTdGF0ZS5zMCI7DQoJc3RhdGU9ICAiaW1sLnBvcnRzLkRlbGF5U3RhdGUuczEiICAmICAgaSA+PSAgbiAgIDogImltbC5wb3J0cy5EZWxheVN0YXRlLnMyIjsNCglUUlVFIDogc3RhdGU7DQplc2FjDQogKSA7DQpUUkFOUyBzX3RyYW5zIDsNCg0KREVGSU5FIGhvbGRzIDo9ICggc3RhdGU9ICAiaW1sLnBvcnRzLkRlbGF5U3RhdGUuczAiICB8ICBzdGF0ZT0gICJpbWwucG9ydHMuRGVsYXlTdGF0ZS5zMSIgICkgOw0KDQpNT0RVTEUgImltbC5sYW5nLlJlYWwiIA0KTU9EVUxFICJVeEFTUmVzcG9uZHNfcGtnRC5yZXNwb25kc19vbmNlIiAoIGEsICBiICkNClZBUiBzIDogeyJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMwIiwiVXhBU1Jlc3BvbmRzX3BrZ0QuUmVzcG9uZHNTdGF0ZS5zMSIsIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczIifSAgOw0KDQpERUZJTkUgc19pbml0IDo9ICggcz0gICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMwIiApIDsNCklOSVQgc19pbml0IDsNCg0KREVGSU5FIHN0YXRlX3RyYW5zIDo9ICggbmV4dChzKT0gIGNhc2UgDQoJcz0gICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMwIiAgJiAgYiAgICYgICFhICA6ICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMxIjsNCglzPSAgIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczAiICAmICBhICA6ICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMyIjsNCglzPSAgIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczEiICAmICBhICA6ICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMwIjsNCglUUlVFIDogczsNCmVzYWMNCiApIDsNClRSQU5TIHN0YXRlX3RyYW5zIDsNCg0KREVGSU5FIGhvbGRzIDo9ICggcz0gICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMwIiAgfCAgcz0gICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMxIiAgKSA7DQoNCk1PRFVMRSAiVXhBU1Jlc3BvbmRzX3BrZ0Qub25lX3JlcXVlc3RfYXRfYV90aW1lIiAoIGEsICBiICkNClZBUiBzIDogeyJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMwIiwiVXhBU1Jlc3BvbmRzX3BrZ0QuUmVzcG9uZHNTdGF0ZS5zMSIsIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczIifSAgOw0KDQpERUZJTkUgc19pbml0IDo9ICggIHMgPSAgIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczAiICApIDsNCklOSVQgc19pbml0IDsNCg0KREVGSU5FIHNfdHJhbnMgOj0gKCBuZXh0KHMpPSAgY2FzZSANCglzPSAgIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczAiICAmICBiICA6ICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMxIjsNCglzPSAgIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczEiICAmICBiICA6ICJVeEFTUmVzcG9uZHNfcGtnRC5SZXNwb25kc1N0YXRlLnMyIjsNCglzPSAgIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczEiICAmICBhICAgJiAgIWIgIDogIlV4QVNSZXNwb25kc19wa2dELlJlc3BvbmRzU3RhdGUuczAiOw0KCVRSVUUgOiBzOw0KZXNhYw0KICkgOw0KVFJBTlMgc190cmFucyA7DQoNCkRFRklORSBob2xkcyA6PSAoIHM9ICAiVXhBU1Jlc3BvbmRzX3BrZ0QuUmVzcG9uZHNTdGF0ZS5zMCIgIHwgIHM9ICAiVXhBU1Jlc3BvbmRzX3BrZ0QuUmVzcG9uZHNTdGF0ZS5zMSIgICkgOw0KDQpNT0RVTEUgImltbC5wb3J0cy5FdmVudERhdGFQb3J0PCBpbWwubGFuZy5Cb29sID4iIA0KVkFSIGRhdGEgOiBib29sZWFuICA7DQpWQVIgZmxvd3BvaW50IDogImltbC5wb3J0cy5GbG93UG9pbnQiICA7DQpWQVIgZXZlbnQgOiBib29sZWFuICA7DQoNCk1PRFVMRSAiVXhBU1Jlc3BvbmRzX3BrZ0QuVXhBU19yZXNwb25kc19kb3RfaSIgKCBBdXRvbWF0aW9uUmVxdWVzdF9pbiwgIEF1dG9tYXRpb25SZXF1ZXN0X2luRiApDQpWQVIgcHJvY2Vzc2luZ19wYXRoRiA6ICJpbWwucG9ydHMuRmxvd1BhdGgiICA7DQpWQVIgVGFza1NlcnZpY2VCYXNlRiA6ICJVeEFTUmVzcG9uZHNfcGtnRC5HZW5lcmljU2VydmljZSIgKFBsYW5CdWlsZGVyRi5TdWJSZXF1ZXN0X291dCxSb3V0ZUFnZ3JlZ2F0b3JGLkNtZFJlc3BvbnNlX291dCkgOw0KVkFSIGRGIDogImltbC5wb3J0cy5kZWxheSIgKHByb2Nlc3NpbmdfcGF0aEYsOSkgOw0KVkFSIGQgOiAiaW1sLnBvcnRzLmRlbGF5IiAocHJvY2Vzc2luZ19wYXRoLDkpIDsNClZBUiBwcm9jZXNzaW5nX3BhdGggOiAiaW1sLnBvcnRzLkZsb3dQYXRoIiAgOw0KVkFSIEF1dG9tYXRpb25SZXF1ZXN0VmFsaWRhdG9yRiA6ICJVeEFTUmVzcG9uZHNfcGtnRC5HZW5lcmljU2VydmljZSIgKEF1dG9tYXRpb25SZXF1ZXN0X2luRixQbGFuQnVpbGRlckYuQ21kUmVzcG9uc2Vfb3V0KSA7DQpWQVIgUGxhbkJ1aWxkZXIgOiAiVXhBU1Jlc3BvbmRzX3BrZ0QuR2VuZXJpY1NlcnZpY2UiIChBdXRvbWF0aW9uUmVxdWVzdFZhbGlkYXRvci5TdWJSZXF1ZXN0X291dCxUYXNrU2VydmljZUJhc2UuQ21kUmVzcG9uc2Vfb3V0KSA7DQpWQVIgQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3IgOiAiVXhBU1Jlc3BvbmRzX3BrZ0QuR2VuZXJpY1NlcnZpY2UiIChBdXRvbWF0aW9uUmVxdWVzdF9pbixQbGFuQnVpbGRlci5DbWRSZXNwb25zZV9vdXQpIDsNClZBUiBBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0RiA6ICJpbWwucG9ydHMuRXZlbnREYXRhUG9ydDwgaW1sLmxhbmcuQm9vbCA+IiAgOw0KVkFSIGFkZWxheW1vbml0b3JGIDogIlV4QVNSZXNwb25kc19wa2dELm9uZV9yZXF1ZXN0X2F0X2FfdGltZSIgKEF1dG9tYXRpb25SZXNwb25zZV9vdXRGLmZsb3dwb2ludC5ldmVudCxBdXRvbWF0aW9uUmVxdWVzdF9pbkYuZmxvd3BvaW50LmV2ZW50KSA7DQpWQVIgUGxhbm5lckYgOiAiVXhBU1Jlc3BvbmRzX3BrZ0QuR2VuZXJpY0xhc3RTZXJ2aWNlTm9EZWxheSIgKFJvdXRlQWdncmVnYXRvckYuU3ViUmVxdWVzdF9vdXQpIDsNClZBUiBBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0IDogImltbC5wb3J0cy5FdmVudERhdGFQb3J0PCBpbWwubGFuZy5Cb29sID4iICA7DQpWQVIgUm91dGVBZ2dyZWdhdG9yRiA6ICJVeEFTUmVzcG9uZHNfcGtnRC5HZW5lcmljU2VydmljZSIgKFRhc2tTZXJ2aWNlQmFzZUYuU3ViUmVxdWVzdF9vdXQsUGxhbm5lckYuQ21kUmVzcG9uc2Vfb3V0KSA7DQpWQVIgYWRlbGF5bW9uaXRvciA6ICJVeEFTUmVzcG9uZHNfcGtnRC5vbmVfcmVxdWVzdF9hdF9hX3RpbWUiIChBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0LmZsb3dwb2ludC5ldmVudCxBdXRvbWF0aW9uUmVxdWVzdF9pbi5mbG93cG9pbnQuZXZlbnQpIDsNClZBUiBUYXNrU2VydmljZUJhc2UgOiAiVXhBU1Jlc3BvbmRzX3BrZ0QuR2VuZXJpY1NlcnZpY2UiIChQbGFuQnVpbGRlci5TdWJSZXF1ZXN0X291dCxSb3V0ZUFnZ3JlZ2F0b3IuQ21kUmVzcG9uc2Vfb3V0KSA7DQpWQVIgYW1vbml0b3JGIDogIlV4QVNSZXNwb25kc19wa2dELm9uZV9yZXF1ZXN0X2F0X2FfdGltZSIgKEF1dG9tYXRpb25SZXNwb25zZV9vdXRGLmV2ZW50LEF1dG9tYXRpb25SZXF1ZXN0X2luRi5ldmVudCkgOw0KVkFSIGdtb25pdG9yIDogIlV4QVNSZXNwb25kc19wa2dELnJlc3BvbmRzX29uY2UiIChBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0LmV2ZW50LEF1dG9tYXRpb25SZXF1ZXN0X2luLmV2ZW50KSA7DQpWQVIgUGxhbm5lciA6ICJVeEFTUmVzcG9uZHNfcGtnRC5HZW5lcmljTGFzdFNlcnZpY2UiIChSb3V0ZUFnZ3JlZ2F0b3IuU3ViUmVxdWVzdF9vdXQpIDsNClZBUiBhbW9uaXRvciA6ICJVeEFTUmVzcG9uZHNfcGtnRC5vbmVfcmVxdWVzdF9hdF9hX3RpbWUiIChBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0LmV2ZW50LEF1dG9tYXRpb25SZXF1ZXN0X2luLmV2ZW50KSA7DQpWQVIgUGxhbkJ1aWxkZXJGIDogIlV4QVNSZXNwb25kc19wa2dELkdlbmVyaWNTZXJ2aWNlIiAoQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3JGLlN1YlJlcXVlc3Rfb3V0LFRhc2tTZXJ2aWNlQmFzZUYuQ21kUmVzcG9uc2Vfb3V0KSA7DQpWQVIgZ21vbml0b3JGIDogIlV4QVNSZXNwb25kc19wa2dELnJlc3BvbmRzX29uY2UiIChBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0Ri5ldmVudCxBdXRvbWF0aW9uUmVxdWVzdF9pbkYuZXZlbnQpIDsNClZBUiBSb3V0ZUFnZ3JlZ2F0b3IgOiAiVXhBU1Jlc3BvbmRzX3BrZ0QuR2VuZXJpY1NlcnZpY2UiIChUYXNrU2VydmljZUJhc2UuU3ViUmVxdWVzdF9vdXQsUGxhbm5lci5DbWRSZXNwb25zZV9vdXQpIDsNCg0KREVGSU5FIGEgOj0gKCBhbW9uaXRvci5ob2xkcyAgJiAgYWRlbGF5bW9uaXRvci5ob2xkcyAgKSA7DQpERUZJTkUgYUYgOj0gKCBhbW9uaXRvckYuaG9sZHMgICYgIGFkZWxheW1vbml0b3JGLmhvbGRzICApIDsNCkRFRklORSBnIDo9ICggZ21vbml0b3IuaG9sZHMgICYgIGQuaG9sZHMgICkgOw0KREVGSU5FIGdGIDo9ICggZ21vbml0b3JGLmhvbGRzICAmICBkRi5ob2xkcyAgKSA7DQoNCklOVkFSICBBdXRvbWF0aW9uUmVxdWVzdFZhbGlkYXRvckYuQ21kUmVzcG9uc2Vfb3V0LmV2ZW50ID0gIEF1dG9tYXRpb25SZXNwb25zZV9vdXRGLmV2ZW50ICYgICBBdXRvbWF0aW9uUmVxdWVzdFZhbGlkYXRvckYuQ21kUmVzcG9uc2Vfb3V0LmRhdGEgPSAgQXV0b21hdGlvblJlc3BvbnNlX291dEYuZGF0YSAmICAgQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3JGLkNtZFJlc3BvbnNlX291dC5mbG93cG9pbnQuZXZlbnQgPSAgQXV0b21hdGlvblJlc3BvbnNlX291dEYuZmxvd3BvaW50LmV2ZW50ICAgOw0KSU5WQVIgKCAoICBwcm9jZXNzaW5nX3BhdGhGLnN0YXJ0LmV2ZW50ID0gIEF1dG9tYXRpb25SZXF1ZXN0X2luRi5ldmVudCAgICYgICBwcm9jZXNzaW5nX3BhdGhGLmVuZC5ldmVudCA9ICBBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0Ri5ldmVudCAgICkgKSAgOw0KSU5WQVIgKCAoICBwcm9jZXNzaW5nX3BhdGguc3RhcnQuZXZlbnQgPSAgQXV0b21hdGlvblJlcXVlc3RfaW4uZXZlbnQgICAmICAgcHJvY2Vzc2luZ19wYXRoLmVuZC5ldmVudCA9ICBBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0LmV2ZW50ICAgKSApICA7DQpJTlZBUiAgQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3IuQ21kUmVzcG9uc2Vfb3V0LmV2ZW50ID0gIEF1dG9tYXRpb25SZXNwb25zZV9vdXQuZXZlbnQgJiAgIEF1dG9tYXRpb25SZXF1ZXN0VmFsaWRhdG9yLkNtZFJlc3BvbnNlX291dC5kYXRhID0gIEF1dG9tYXRpb25SZXNwb25zZV9vdXQuZGF0YSAmICAgQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3IuQ21kUmVzcG9uc2Vfb3V0LmZsb3dwb2ludC5ldmVudCA9ICBBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0LmZsb3dwb2ludC5ldmVudCAgIDsNCg0KTU9EVUxFICJVeEFTUmVzcG9uZHNfcGtnRC5VeEFTX3Jlc3BvbmRzIiAoIEF1dG9tYXRpb25SZXF1ZXN0X2luLCAgQXV0b21hdGlvblJlcXVlc3RfaW5GICkNClZBUiBwcm9jZXNzaW5nX3BhdGhGIDogImltbC5wb3J0cy5GbG93UGF0aCIgIDsNClZBUiBBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0RiA6ICJpbWwucG9ydHMuRXZlbnREYXRhUG9ydDwgaW1sLmxhbmcuQm9vbCA+IiAgOw0KVkFSIGFkZWxheW1vbml0b3JGIDogIlV4QVNSZXNwb25kc19wa2dELm9uZV9yZXF1ZXN0X2F0X2FfdGltZSIgKEF1dG9tYXRpb25SZXNwb25zZV9vdXRGLmZsb3dwb2ludC5ldmVudCxBdXRvbWF0aW9uUmVxdWVzdF9pbkYuZmxvd3BvaW50LmV2ZW50KSA7DQpWQVIgZEYgOiAiaW1sLnBvcnRzLmRlbGF5IiAocHJvY2Vzc2luZ19wYXRoRiw5KSA7DQpWQVIgQXV0b21hdGlvblJlc3BvbnNlX291dCA6ICJpbWwucG9ydHMuRXZlbnREYXRhUG9ydDwgaW1sLmxhbmcuQm9vbCA+IiAgOw0KVkFSIGQgOiAiaW1sLnBvcnRzLmRlbGF5IiAocHJvY2Vzc2luZ19wYXRoLDkpIDsNClZBUiBhZGVsYXltb25pdG9yIDogIlV4QVNSZXNwb25kc19wa2dELm9uZV9yZXF1ZXN0X2F0X2FfdGltZSIgKEF1dG9tYXRpb25SZXNwb25zZV9vdXQuZmxvd3BvaW50LmV2ZW50LEF1dG9tYXRpb25SZXF1ZXN0X2luLmZsb3dwb2ludC5ldmVudCkgOw0KVkFSIHByb2Nlc3NpbmdfcGF0aCA6ICJpbWwucG9ydHMuRmxvd1BhdGgiICA7DQpWQVIgYW1vbml0b3JGIDogIlV4QVNSZXNwb25kc19wa2dELm9uZV9yZXF1ZXN0X2F0X2FfdGltZSIgKEF1dG9tYXRpb25SZXNwb25zZV9vdXRGLmV2ZW50LEF1dG9tYXRpb25SZXF1ZXN0X2luRi5ldmVudCkgOw0KVkFSIGdtb25pdG9yIDogIlV4QVNSZXNwb25kc19wa2dELnJlc3BvbmRzX29uY2UiIChBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0LmV2ZW50LEF1dG9tYXRpb25SZXF1ZXN0X2luLmV2ZW50KSA7DQpWQVIgYW1vbml0b3IgOiAiVXhBU1Jlc3BvbmRzX3BrZ0Qub25lX3JlcXVlc3RfYXRfYV90aW1lIiAoQXV0b21hdGlvblJlc3BvbnNlX291dC5ldmVudCxBdXRvbWF0aW9uUmVxdWVzdF9pbi5ldmVudCkgOw0KVkFSIGdtb25pdG9yRiA6ICJVeEFTUmVzcG9uZHNfcGtnRC5yZXNwb25kc19vbmNlIiAoQXV0b21hdGlvblJlc3BvbnNlX291dEYuZXZlbnQsQXV0b21hdGlvblJlcXVlc3RfaW5GLmV2ZW50KSA7DQoNCkRFRklORSBhIDo9ICggYW1vbml0b3IuaG9sZHMgICYgIGFkZWxheW1vbml0b3IuaG9sZHMgICkgOw0KREVGSU5FIGFGIDo9ICggYW1vbml0b3JGLmhvbGRzICAmICBhZGVsYXltb25pdG9yRi5ob2xkcyAgKSA7DQpERUZJTkUgZyA6PSAoIGdtb25pdG9yLmhvbGRzICAmICBkLmhvbGRzICApIDsNCkRFRklORSBnRiA6PSAoIGdtb25pdG9yRi5ob2xkcyAgJiAgZEYuaG9sZHMgICkgOw0KDQpJTlZBUiAoICggIHByb2Nlc3NpbmdfcGF0aEYuc3RhcnQuZXZlbnQgPSAgQXV0b21hdGlvblJlcXVlc3RfaW5GLmV2ZW50ICAgJiAgIHByb2Nlc3NpbmdfcGF0aEYuZW5kLmV2ZW50ID0gIEF1dG9tYXRpb25SZXNwb25zZV9vdXRGLmV2ZW50ICAgKSApICA7DQpJTlZBUiAoICggIHByb2Nlc3NpbmdfcGF0aC5zdGFydC5ldmVudCA9ICBBdXRvbWF0aW9uUmVxdWVzdF9pbi5ldmVudCAgICYgICBwcm9jZXNzaW5nX3BhdGguZW5kLmV2ZW50ID0gIEF1dG9tYXRpb25SZXNwb25zZV9vdXQuZXZlbnQgICApICkgIDsNCg0KTU9EVUxFICJpbWwucG9ydHMuRmxvd1BhdGgiIA0KVkFSIHVwcGVyQm91bmQgOiAiaW1sLmxhbmcuUmVhbCIgIDsNClZBUiBzdGFydCA6ICJpbWwucG9ydHMuRmxvd1BvaW50IiAgOw0KVkFSIGVuZCA6ICJpbWwucG9ydHMuRmxvd1BvaW50IiAgOw0KVkFSIGxvd2VyQm91bmQgOiAiaW1sLmxhbmcuUmVhbCIgIDsNCg0KTU9EVUxFICJVeEFTUmVzcG9uZHNfcGtnRC5HZW5lcmljU2VydmljZSIgKCBDbWRSZXF1ZXN0X2luLCAgU3ViUmVzcG9uc2VfaW4gKQ0KVkFSIGcxbW9uaXRvciA6ICJVeEFTUmVzcG9uZHNfcGtnRC5yZXNwb25kc19vbmNlIiAoU3ViUmVxdWVzdF9vdXQuZXZlbnQsQ21kUmVxdWVzdF9pbi5ldmVudCkgOw0KVkFSIHByb2Nlc3NpbmdfcGF0aDEgOiAiaW1sLnBvcnRzLkZsb3dQYXRoIiAgOw0KVkFSIENtZFJlc3BvbnNlX291dCA6ICJpbWwucG9ydHMuRXZlbnREYXRhUG9ydDwgaW1sLmxhbmcuQm9vbCA+IiAgOw0KVkFSIFN1YlJlcXVlc3Rfb3V0IDogImltbC5wb3J0cy5FdmVudERhdGFQb3J0PCBpbWwubGFuZy5Cb29sID4iICA7DQpWQVIgcHJvY2Vzc2luZ19wYXRoMCA6ICJpbWwucG9ydHMuRmxvd1BhdGgiICA7DQpWQVIgZzJtb25pdG9yIDogIlV4QVNSZXNwb25kc19wa2dELnJlc3BvbmRzX29uY2UiIChDbWRSZXNwb25zZV9vdXQuZXZlbnQsU3ViUmVzcG9uc2VfaW4uZXZlbnQpIDsNClZBUiBkMSA6ICJpbWwucG9ydHMuZGVsYXkiIChwcm9jZXNzaW5nX3BhdGgwLDEpIDsNClZBUiBkMiA6ICJpbWwucG9ydHMuZGVsYXkiIChwcm9jZXNzaW5nX3BhdGgxLDEpIDsNCg0KREVGSU5FIGcgOj0gKCBnMW1vbml0b3IuaG9sZHMgICYgIGcybW9uaXRvci5ob2xkcyAgICYgIGQxLmhvbGRzICAgJiAgZDIuaG9sZHMgICkgOw0KDQpJTlZBUiAoICggIHByb2Nlc3NpbmdfcGF0aDEuc3RhcnQuZXZlbnQgPSAgU3ViUmVzcG9uc2VfaW4uZXZlbnQgICAmICAgcHJvY2Vzc2luZ19wYXRoMS5lbmQuZXZlbnQgPSAgQ21kUmVzcG9uc2Vfb3V0LmV2ZW50ICAgKSApICA7DQpJTlZBUiAoICggIHByb2Nlc3NpbmdfcGF0aDAuc3RhcnQuZXZlbnQgPSAgQ21kUmVxdWVzdF9pbi5ldmVudCAgICYgICBwcm9jZXNzaW5nX3BhdGgwLmVuZC5ldmVudCA9ICBTdWJSZXF1ZXN0X291dC5ldmVudCAgICkgKSAgOw0KDQpNT0RVTEUgImltbC5wb3J0cy5Qb3J0IiANCg0KCk1PRFVMRSBtYWluIA0KVkFSIEF1dG9tYXRpb25SZXF1ZXN0X2luRiA6ICJpbWwucG9ydHMuRXZlbnREYXRhUG9ydDwgaW1sLmxhbmcuQm9vbCA+IiAgOw0KVkFSIGluc3QgOiAiVXhBU1Jlc3BvbmRzX3BrZ0QuVXhBU19yZXNwb25kc19kb3RfaSIgKEF1dG9tYXRpb25SZXF1ZXN0X2luLEF1dG9tYXRpb25SZXF1ZXN0X2luRikgOw0KVkFSIEF1dG9tYXRpb25SZXF1ZXN0X2luIDogImltbC5wb3J0cy5FdmVudERhdGFQb3J0PCBpbWwubGFuZy5Cb29sID4iICA7DQoNCg== ) 
( edge E_2 __ ( N_1 property ) :type nusmv :encoding base64 :content TFRMU1BFQyAhRyhpbnN0LmEgICYgIGluc3QuYUYgICAmICAoIFRSVUUgIC0+ICBpbnN0LkF1dG9tYXRpb25SZXF1ZXN0VmFsaWRhdG9yLmcgICkgICAmICAoIFRSVUUgIC0+ICBpbnN0LlBsYW5CdWlsZGVyLmcgICkgICAmICAoIFRSVUUgIC0+ICBpbnN0LlRhc2tTZXJ2aWNlQmFzZS5nICApICAgJiAgKCBUUlVFICAtPiAgaW5zdC5Sb3V0ZUFnZ3JlZ2F0b3IuZyAgKSAgICYgICggVFJVRSAgLT4gIGluc3QuUGxhbm5lci5nICApICAgJiAgKCBUUlVFICAtPiAgaW5zdC5BdXRvbWF0aW9uUmVxdWVzdFZhbGlkYXRvckYuZyAgKSAgICYgICggVFJVRSAgLT4gIGluc3QuUGxhbkJ1aWxkZXJGLmcgICkgICAmICAoIFRSVUUgIC0+ICBpbnN0LlRhc2tTZXJ2aWNlQmFzZUYuZyAgKSAgICYgICggVFJVRSAgLT4gIGluc3QuUm91dGVBZ2dyZWdhdG9yRi5nICApICAgJiAgKCBUUlVFICAtPiAgaW5zdC5QbGFubmVyRi5nICApICkgfCBHKGluc3QuZyAgJiAgaW5zdC5nRiApIDsg ) 
( edge E_3 ( N_1 holds ) 
( N_4 in ) :type boolX :encoding base64 :content __ ) 
( edge E_4 ( N_1 cexample ) __ :type nusmv :encoding base64 :content __ ) 
( edge E_21 ( N_3 holds ) 
( N_4 in ) :type boolX :encoding base64 :content __ ) 
( edge E_23 ( N_4 out ) 
( N_5 in ) :type boolX :encoding base64 :content __ ) 
( edge E_19 __ ( N_3 delayspec ) :type delay :encoding base64 :content QXV0b21hdGlvblJlcXVlc3RfaW4gOiBBdXRvbWF0aW9uUmVzcG9uc2Vfb3V0IDogOQ== ) 
( edge E_20 __ ( N_3 delaypath ) :type delay :encoding base64 :content Y29ubmVjdGlvbiA6IEF1dG9tYXRpb25SZXF1ZXN0X2luIDogQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3IuQ21kUmVxdWVzdF9pbiA6IDAKZmxvdyA6IEF1dG9tYXRpb25SZXF1ZXN0VmFsaWRhdG9yIDogQ21kUmVxdWVzdF9pbiA6IFN1YlJlcXVlc3Rfb3V0IDogMQpjb25uZWN0aW9uIDogQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3IuU3ViUmVxdWVzdF9vdXQgOiBQbGFuQnVpbGRlci5DbWRSZXF1ZXN0X2luIDogMApmbG93IDogUGxhbkJ1aWxkZXIgOiBDbWRSZXF1ZXN0X2luIDogU3ViUmVxdWVzdF9vdXQgOiAxCmNvbm5lY3Rpb24gOiBQbGFuQnVpbGRlci5TdWJSZXF1ZXN0X291dCA6IFRhc2tTZXJ2aWNlQmFzZS5DbWRSZXF1ZXN0X2luIDogMApmbG93IDogVGFza1NlcnZpY2VCYXNlIDogQ21kUmVxdWVzdF9pbiA6IFN1YlJlcXVlc3Rfb3V0IDogMQpjb25uZWN0aW9uIDogVGFza1NlcnZpY2VCYXNlLlN1YlJlcXVlc3Rfb3V0IDogUm91dGVBZ2dyZWdhdG9yLkNtZFJlcXVlc3RfaW4gOiAwCmZsb3cgOiBSb3V0ZUFnZ3JlZ2F0b3IgOiBDbWRSZXF1ZXN0X2luIDogU3ViUmVxdWVzdF9vdXQgOiAxCmNvbm5lY3Rpb24gOiBSb3V0ZUFnZ3JlZ2F0b3IuU3ViUmVxdWVzdF9vdXQgOiBQbGFubmVyLkNtZFJlcXVlc3RfaW4gOiAwCmZsb3cgOiBQbGFubmVyIDogQ21kUmVxdWVzdF9pbiA6IENtZFJlc3BvbnNlX291dCA6IDEKY29ubmVjdGlvbiA6IFBsYW5uZXIuQ21kUmVzcG9uc2Vfb3V0IDogUm91dGVBZ2dyZWdhdG9yLlN1YlJlc3BvbnNlX2luIDogMApmbG93IDogUm91dGVBZ2dyZWdhdG9yIDogU3ViUmVzcG9uc2VfaW4gOiBDbWRSZXNwb25zZV9vdXQgOiAxCmNvbm5lY3Rpb24gOiBSb3V0ZUFnZ3JlZ2F0b3IuQ21kUmVzcG9uc2Vfb3V0IDogVGFza1NlcnZpY2VCYXNlLlN1YlJlc3BvbnNlX2luIDogMApmbG93IDogVGFza1NlcnZpY2VCYXNlIDogU3ViUmVzcG9uc2VfaW4gOiBDbWRSZXNwb25zZV9vdXQgOiAxCmNvbm5lY3Rpb24gOiBUYXNrU2VydmljZUJhc2UuQ21kUmVzcG9uc2Vfb3V0IDogUGxhbkJ1aWxkZXIuU3ViUmVzcG9uc2VfaW4gOiAwCmZsb3cgOiBQbGFuQnVpbGRlciA6IFN1YlJlc3BvbnNlX2luIDogQ21kUmVzcG9uc2Vfb3V0IDogMQpjb25uZWN0aW9uIDogUGxhbkJ1aWxkZXIuQ21kUmVzcG9uc2Vfb3V0IDogQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3IuU3ViUmVzcG9uc2VfaW4gOiAwCmZsb3cgOiBBdXRvbWF0aW9uUmVxdWVzdFZhbGlkYXRvciA6IFN1YlJlc3BvbnNlX2luIDogQ21kUmVzcG9uc2Vfb3V0IDogMQpjb25uZWN0aW9uIDogQXV0b21hdGlvblJlcXVlc3RWYWxpZGF0b3IuQ21kUmVzcG9uc2Vfb3V0IDogQXV0b21hdGlvblJlc3BvbnNlX291dCA6IDAK ) 
( edge E_22 ( N_3 explanation ) __ :type delay :encoding base64 :content __ ) ) )
