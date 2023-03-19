include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wbr.mm"
include "cv.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "ressxr.mm"
include "sstr.mm"
include "mpan2.mm"
include "wi.mm"
include "supxrcl.mm"
include "wa.mm"
include "pnfxr.mm"
include "xrltne.mm"
include "mp3an2.mm"
include "necomd.mm"
include "ex.mm"
include "syl.mm"
include "wceq.mm"
include "wn.mm"
include "supxrunb2.mm"
include "wb.mm"
include "ssel2.mm"
include "adantlr.mm"
include "rexr.mm"
include "ad2antlr.mm"
include "xrlenlt.mm"
include "con2bid.mm"
include "syl2anc.mm"
include "rexbidva.mm"
include "rexnal.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "bitr3d.mm"
include "ralnex.mm"
include "necon2abid.mm"
include "sylibrd.mm"
include "imp.mm"
include "sylan.mm"
include "3adant2.mm"
include "w3a.mm"
include "supxrre.mm"
include "suprcl.mm"
include "eqeltrd.mm"
include "syld3an3.mm"

theorem supxrbnd
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B


  assert |- ( ( A C_ RR /\ A =/= (/) /\ sup ( A , RR* , < ) < +oo ) -> sup ( A , RR* , < ) e. RR )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    cA
    cxr
    clt
    csup
    #
    cpnf
    clt
    wbr
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    @2
    cr
    wcel
    @0
    @3
    @8
    @1
    @0
    cA
    cxr
    wss
    #
    @3
    @8
    @0
    cr
    cxr
    wss
    @9
    ressxr
    cA
    cr
    cxr
    sstr
    mpan2
    @9
    @3
    @8
    @9
    @3
    @2
    cpnf
    wne
    #
    @8
    @9
    @2
    cxr
    wcel
    #
    @3
    @10
    wi
    cA
    supxrcl
    @11
    @3
    @10
    @11
    @3
    wa
    cpnf
    @2
    @11
    cpnf
    cxr
    wcel
    @3
    cpnf
    @2
    wne
    pnfxr
    @2
    cpnf
    xrltne
    mp3an2
    necomd
    ex
    syl
    @9
    @8
    @2
    cpnf
    @9
    @2
    cpnf
    wceq
    #
    @7
    wn
    #
    vx
    cr
    wral
    #
    @8
    wn
    @9
    @5
    @4
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cr
    wral
    @12
    @14
    vx
    vy
    cA
    supxrunb2
    @9
    @16
    @13
    vx
    cr
    @9
    @5
    cr
    wcel
    #
    wa
    #
    @16
    @6
    wn
    #
    vy
    cA
    wrex
    @13
    @18
    @15
    @19
    vy
    cA
    @18
    @4
    cA
    wcel
    #
    wa
    @4
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @15
    @19
    wb
    @9
    @20
    @21
    @17
    cA
    cxr
    @4
    ssel2
    adantlr
    @17
    @22
    @9
    @20
    @5
    rexr
    ad2antlr
    @21
    @22
    wa
    @6
    @15
    @4
    @5
    xrlenlt
    con2bid
    syl2anc
    rexbidva
    @6
    vy
    cA
    rexnal
    syl6bb
    ralbidva
    bitr3d
    @7
    vx
    cr
    ralnex
    syl6bb
    necon2abid
    sylibrd
    imp
    sylan
    3adant2
    @0
    @1
    @8
    w3a
    @2
    cA
    cr
    clt
    csup
    cr
    vx
    vy
    cA
    supxrre
    vx
    vy
    cA
    suprcl
    eqeltrd
    syld3an3
end
