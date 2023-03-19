include "con0.mm"
include "wrex.mm"
include "wsb.mm"
include "wn.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "cint.mm"
include "wcel.mm"
include "wsbc.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "rabn0.mm"
include "biimpri.mm"
include "oninton.mm"
include "sylancr.mm"
include "onminesb.mm"
include "onss.mm"
include "syl.mm"
include "sseld.mm"
include "onnminsb.mm"
include "syli.mm"
include "ralrimiv.mm"
include "wceq.mm"
include "dfsbcq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfan.mm"
include "weq.mm"
include "sbequ12.mm"
include "cbvrex.mm"
include "sylibr.mm"

theorem onminex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume onminex.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( E. x e. On ph -> E. x e. On ( ph /\ A. y e. x -. ps ) )

  proof
    wph
    vx
    con0
    wrex
    #
    wph
    vx
    vz
    wsb
    #
    wps
    wn
    #
    vy
    vz
    cv
    #
    wral
    #
    wa
    #
    vz
    con0
    wrex
    #
    wph
    @2
    vy
    vx
    cv
    #
    wral
    #
    wa
    #
    vx
    con0
    wrex
    @0
    wph
    vx
    con0
    crab
    #
    cint
    #
    con0
    wcel
    #
    wph
    vx
    @11
    wsbc
    #
    @2
    vy
    @11
    wral
    #
    @6
    @0
    @10
    con0
    wss
    @10
    c0
    wne
    #
    @12
    wph
    vx
    con0
    ssrab2
    @15
    @0
    wph
    vx
    con0
    rabn0
    biimpri
    @10
    oninton
    sylancr
    #
    wph
    vx
    onminesb
    @0
    @2
    vy
    @11
    vy
    cv
    #
    @11
    wcel
    @0
    @17
    con0
    wcel
    @2
    @0
    @11
    con0
    @17
    @0
    @12
    @11
    con0
    wss
    @16
    @11
    onss
    syl
    sseld
    wph
    wps
    vx
    @17
    onminex.1
    onnminsb
    syli
    ralrimiv
    @5
    @13
    @14
    wa
    vz
    @11
    con0
    @3
    @11
    wceq
    @1
    @13
    @4
    @14
    wph
    vx
    vz
    @11
    dfsbcq2
    @2
    vy
    @3
    @11
    raleq
    anbi12d
    rspcev
    syl12anc
    @9
    @5
    vx
    vz
    con0
    @9
    vz
    nfv
    @1
    @4
    vx
    wph
    vx
    vz
    nfs1v
    @4
    vx
    nfv
    nfan
    vx
    vz
    weq
    wph
    @1
    @8
    @4
    wph
    vx
    vz
    sbequ12
    @2
    vy
    @7
    @3
    raleq
    anbi12d
    cbvrex
    sylibr
end
