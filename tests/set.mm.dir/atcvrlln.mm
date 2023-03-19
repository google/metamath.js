include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "simpll1.mm"
include "simpll3.mm"
include "simpr.mm"
include "simplr.mm"
include "llni.mm"
include "syl31anc.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "eqid.mm"
include "islln3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wi.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp1r.mm"
include "simp3r.mm"
include "breqtrd.mm"
include "cvrat2.mm"
include "syl132anc.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "adantr.mm"
include "mpd.mm"
include "impbida.mm"

theorem atcvrlln
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  assume atcvrlln.b: |- B = ( Base ` K )
  assume atcvrlln.c: |- C = ( <o ` K )
  assume atcvrlln.a: |- A = ( Atoms ` K )
  assume atcvrlln.n: |- N = ( LLines ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ X C Y ) -> ( X e. A <-> Y e. N ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    cC
    wbr
    #
    wa
    #
    cX
    cA
    wcel
    #
    cY
    cN
    wcel
    #
    @5
    @6
    wa
    @0
    @2
    @6
    @4
    @7
    @0
    @1
    @2
    @4
    @6
    simpll1
    @0
    @1
    @2
    @4
    @6
    simpll3
    @5
    @6
    simpr
    @3
    @4
    @6
    simplr
    cA
    cB
    cC
    chlt
    cX
    cK
    cN
    cY
    atcvrlln.b
    atcvrlln.c
    atcvrlln.a
    atcvrlln.n
    llni
    syl31anc
    @5
    @7
    wa
    #
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    cY
    @9
    @10
    cK
    cjn
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    #
    @6
    @8
    @7
    @16
    @5
    @7
    simpr
    @8
    @0
    @2
    @7
    @16
    wb
    @0
    @1
    @2
    @4
    @7
    simpll1
    @0
    @1
    @2
    @4
    @7
    simpll3
    cA
    cB
    @12
    cK
    cN
    cY
    vq
    vp
    atcvrlln.b
    @12
    eqid
    #
    atcvrlln.a
    atcvrlln.n
    islln3
    syl2anc
    mpbid
    @5
    @16
    @6
    wi
    @7
    @5
    @15
    @6
    vp
    vq
    cA
    cA
    @5
    @9
    cA
    wcel
    #
    @10
    cA
    wcel
    #
    wa
    #
    @15
    @6
    @5
    @20
    @15
    w3a
    #
    @0
    @1
    @18
    @19
    @11
    cX
    @13
    cC
    wbr
    @6
    @0
    @1
    @2
    @4
    @20
    @15
    simp1l1
    @0
    @1
    @2
    @4
    @20
    @15
    simp1l2
    @5
    @18
    @19
    @15
    simp2l
    @5
    @18
    @19
    @15
    simp2r
    @5
    @20
    @11
    @14
    simp3l
    @21
    cX
    cY
    @13
    cC
    @3
    @4
    @20
    @15
    simp1r
    @5
    @20
    @11
    @14
    simp3r
    breqtrd
    cA
    cB
    cC
    @9
    @10
    @12
    cK
    cX
    atcvrlln.b
    @17
    atcvrlln.c
    atcvrlln.a
    cvrat2
    syl132anc
    3exp
    rexlimdvv
    adantr
    mpd
    impbida
end
