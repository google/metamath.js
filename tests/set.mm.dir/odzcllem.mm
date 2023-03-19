include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "codz.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "odzval.mm"
include "cuz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "wrex.mm"
include "cphi.mm"
include "phicl.mm"
include "3ad2ant1.mm"
include "cmo.mm"
include "eulerth.mm"
include "wb.mm"
include "simp1.mm"
include "cn0.mm"
include "simp2.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "1z.mm"
include "moddvds.mm"
include "mp3an3.mm"
include "mpbid.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "rspcev.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "elrab.mm"
include "sylib.mm"

theorem odzcllem
  let cA: class A
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cK: class K


  assert |- ( ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 ) -> ( ( ( odZ ` N ) ` A ) e. NN /\ N || ( ( A ^ ( ( odZ ` N ) ` A ) ) - 1 ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cN
    cgcd
    co
    c1
    wceq
    #
    w3a
    #
    cA
    cN
    codz
    cfv
    cfv
    #
    cN
    cA
    vn
    cv
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    wcel
    @4
    cn
    wcel
    cN
    cA
    @4
    cexp
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    @3
    @4
    @9
    cr
    clt
    cinf
    #
    @9
    cA
    vn
    cN
    odzval
    @3
    @9
    c1
    cuz
    cfv
    #
    wss
    @9
    c0
    wne
    #
    @13
    @9
    wcel
    @9
    cn
    @14
    @8
    vn
    cn
    ssrab2
    nnuz
    sseqtri
    @3
    @8
    vn
    cn
    wrex
    #
    @15
    @3
    cN
    cphi
    cfv
    #
    cn
    wcel
    #
    cN
    cA
    @17
    cexp
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    @16
    @0
    @1
    @18
    @2
    cN
    phicl
    3ad2ant1
    #
    @3
    @19
    cN
    cmo
    co
    c1
    cN
    cmo
    co
    wceq
    #
    @21
    cA
    cN
    eulerth
    @3
    @0
    @19
    cz
    wcel
    #
    @23
    @21
    wb
    #
    @0
    @1
    @2
    simp1
    @3
    @1
    @17
    cn0
    wcel
    @24
    @0
    @1
    @2
    simp2
    @3
    @17
    @22
    nnnn0d
    cA
    @17
    zexpcl
    syl2anc
    @0
    @24
    c1
    cz
    wcel
    @25
    1z
    @19
    c1
    cN
    moddvds
    mp3an3
    syl2anc
    mpbid
    @8
    @21
    vn
    @17
    cn
    @5
    @17
    wceq
    #
    @7
    @20
    cN
    cdvds
    @26
    @6
    @19
    c1
    cmin
    @5
    @17
    cA
    cexp
    oveq2
    oveq1d
    breq2d
    rspcev
    syl2anc
    @8
    vn
    cn
    rabn0
    sylibr
    @9
    c1
    infssuzcl
    sylancr
    eqeltrd
    @8
    @12
    vn
    @4
    cn
    @5
    @4
    wceq
    #
    @7
    @11
    cN
    cdvds
    @27
    @6
    @10
    c1
    cmin
    @5
    @4
    cA
    cexp
    oveq2
    oveq1d
    breq2d
    elrab
    sylib
end
