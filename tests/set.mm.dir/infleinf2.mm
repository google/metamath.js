include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "nfv.mm"
include "nfan.mm"
include "w3a.mm"
include "infxrcld.mm"
include "3ad2ant1.mm"
include "3adant1r.mm"
include "sselda.mm"
include "3adant3.mm"
include "wss.mm"
include "adantr.mm"
include "simpr.mm"
include "infxrlb.mm"
include "syl2anc.mm"
include "simp3.mm"
include "xrletrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ralrimia.mm"
include "wb.mm"
include "infxrgelb.mm"
include "mpbird.mm"

theorem infleinf2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume infleinf2.x: |- F/ x ph
  assume infleinf2.p: |- F/ y ph
  assume infleinf2.a: |- ( ph -> A C_ RR* )
  assume infleinf2.b: |- ( ph -> B C_ RR* )
  assume infleinf2.y: |- ( ( ph /\ x e. B ) -> E. y e. A y <_ x )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( ph -> inf ( A , RR* , < ) <_ inf ( B , RR* , < ) )

  proof
    wph
    cA
    cxr
    clt
    cinf
    #
    cB
    cxr
    clt
    cinf
    cle
    wbr
    #
    @0
    vx
    cv
    #
    cle
    wbr
    #
    vx
    cB
    wral
    #
    wph
    @3
    vx
    cB
    infleinf2.x
    wph
    @2
    cB
    wcel
    #
    wa
    #
    vy
    cv
    #
    @2
    cle
    wbr
    #
    vy
    cA
    wrex
    @3
    infleinf2.y
    @6
    @8
    @3
    vy
    cA
    wph
    @5
    vy
    infleinf2.p
    @5
    vy
    nfv
    nfan
    @3
    vy
    nfv
    @6
    @7
    cA
    wcel
    #
    @8
    @3
    @6
    @9
    @8
    w3a
    @0
    @7
    @2
    wph
    @9
    @8
    @0
    cxr
    wcel
    #
    @5
    wph
    @9
    @10
    @8
    wph
    cA
    infleinf2.a
    infxrcld
    #
    3ad2ant1
    3adant1r
    wph
    @9
    @8
    @7
    cxr
    wcel
    #
    @5
    wph
    @9
    @12
    @8
    wph
    cA
    cxr
    @7
    infleinf2.a
    sselda
    3adant3
    3adant1r
    @6
    @9
    @2
    cxr
    wcel
    @8
    wph
    cB
    cxr
    @2
    infleinf2.b
    sselda
    3ad2ant1
    wph
    @9
    @8
    @0
    @7
    cle
    wbr
    #
    @5
    wph
    @9
    @13
    @8
    wph
    @9
    wa
    cA
    cxr
    wss
    #
    @9
    @13
    wph
    @14
    @9
    infleinf2.a
    adantr
    wph
    @9
    simpr
    cA
    @7
    infxrlb
    syl2anc
    3adant3
    3adant1r
    @6
    @9
    @8
    simp3
    xrletrd
    3exp
    rexlimd
    mpd
    ralrimia
    wph
    cB
    cxr
    wss
    @10
    @1
    @4
    wb
    infleinf2.b
    @11
    vx
    cB
    @0
    infxrgelb
    syl2anc
    mpbird
end
