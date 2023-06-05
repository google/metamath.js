include "wn.mm";
include "wa.mm";
include "wo.mm";
include "olc.mm";
include "expcom.mm";
include "pm2.21.mm";
include "adantld.mm";
include "wi.mm";
include "simpl.mm";
include "a1i.mm";
include "jaod.mm";
include "impbid.mm";

theorem dedlemb(wph: wff ph, wps: wff ps, wch: wff ch) {





  do {
    wph;
    wn;
    #;
    wch;
    wps;
    wph;
    wa;
    #;
    wch;
    @0;
    wa;
    #;
    wo;
    #;
    wch;
    @0;
    @3;
    @2;
    @1;
    olc;
    expcom;
    @0;
    @1;
    wch;
    @2;
    @0;
    wph;
    wch;
    wps;
    wph;
    wch;
    pm2.21;
    adantld;
    @2;
    wch;
    wi;
    @0;
    wch;
    @0;
    simpl;
    a1i;
    jaod;
    impbid;
  };

  return |- "( -. ph -> ( ch <-> ( ( ps /\\ ph ) \\/ ( ch /\\ -. ph ) ) ) )";
}
