include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "co.mm"
include "coc.mm"
include "cfv.mm"
include "cp0.mm"
include "wceq.mm"
include "simprr.mm"
include "wb.mm"
include "cvr1.mm"
include "adantr.mm"
include "mpbid.mm"
include "cops.mm"
include "simpl1.mm"
include "hlop.mm"
include "syl.mm"
include "simpl2.mm"
include "clat.mm"
include "hllat.mm"
include "simpl3.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "cvrcon3b.mm"
include "cal.mm"
include "hlatl.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "opoc1.mm"
include "3syl.mm"
include "simprl.mm"
include "op1cl.mm"
include "eqbrtrrd.mm"
include "isat.mm"
include "mpbir2and.mm"
include "atcvreq0.mm"
include "fveq2d.mm"
include "opococ.mm"
include "opoc0.mm"
include "3eqtr3d.mm"

theorem 1cvrjat
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.1: class .1.
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume 1cvrjat.b: |- B = ( Base ` K )
  assume 1cvrjat.l: |- .<_ = ( le ` K )
  assume 1cvrjat.j: |- .\/ = ( join ` K )
  assume 1cvrjat.u: |- .1. = ( 1. ` K )
  assume 1cvrjat.c: |- C = ( <o ` K )
  assume 1cvrjat.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ P e. A ) /\ ( X C .1. /\ -. P .<_ X ) ) -> ( X .\/ P ) = .1. )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    c.1
    cC
    wbr
    #
    cP
    cX
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cX
    cP
    c.or
    co
    #
    cK
    coc
    cfv
    #
    cfv
    #
    @9
    cfv
    #
    cK
    cp0
    cfv
    #
    @9
    cfv
    #
    @8
    c.1
    @7
    @10
    @12
    @9
    @7
    @10
    cX
    @9
    cfv
    #
    cC
    wbr
    #
    @10
    @12
    wceq
    #
    @7
    cX
    @8
    cC
    wbr
    #
    @15
    @7
    @5
    @17
    @3
    @4
    @5
    simprr
    @3
    @5
    @17
    wb
    @6
    cA
    cB
    cC
    cP
    c.or
    cK
    c.le
    cX
    1cvrjat.b
    1cvrjat.l
    1cvrjat.j
    1cvrjat.c
    1cvrjat.a
    cvr1
    adantr
    mpbid
    @7
    cK
    cops
    wcel
    #
    @1
    @8
    cB
    wcel
    #
    @17
    @15
    wb
    @7
    @0
    @18
    @0
    @1
    @2
    @6
    simpl1
    #
    cK
    hlop
    #
    syl
    #
    @0
    @1
    @2
    @6
    simpl2
    #
    @7
    cK
    clat
    wcel
    #
    @1
    cP
    cB
    wcel
    #
    @19
    @7
    @0
    @24
    @20
    cK
    hllat
    syl
    @23
    @7
    @2
    @25
    @0
    @1
    @2
    @6
    simpl3
    cA
    cB
    cP
    cK
    1cvrjat.b
    1cvrjat.a
    atbase
    syl
    cB
    c.or
    cK
    cX
    cP
    1cvrjat.b
    1cvrjat.j
    latjcl
    syl3anc
    #
    cB
    cC
    cK
    @9
    cX
    @8
    1cvrjat.b
    @9
    eqid
    #
    1cvrjat.c
    cvrcon3b
    syl3anc
    mpbid
    @7
    cK
    cal
    wcel
    #
    @10
    cB
    wcel
    #
    @14
    cA
    wcel
    #
    @15
    @16
    wb
    @7
    @0
    @28
    @20
    cK
    hlatl
    syl
    @7
    @18
    @19
    @29
    @22
    @26
    cB
    cK
    @9
    @8
    1cvrjat.b
    @27
    opoccl
    syl2anc
    @7
    @30
    @14
    cB
    wcel
    #
    @12
    @14
    cC
    wbr
    #
    @7
    @18
    @1
    @31
    @22
    @23
    cB
    cK
    @9
    cX
    1cvrjat.b
    @27
    opoccl
    syl2anc
    @7
    c.1
    @9
    cfv
    #
    @12
    @14
    cC
    @7
    @0
    @18
    @33
    @12
    wceq
    @20
    @21
    c.1
    cK
    @9
    @12
    @12
    eqid
    #
    1cvrjat.u
    @27
    opoc1
    3syl
    @7
    @4
    @33
    @14
    cC
    wbr
    #
    @3
    @4
    @5
    simprl
    @7
    @18
    @1
    c.1
    cB
    wcel
    #
    @4
    @35
    wb
    @22
    @23
    @7
    @0
    @18
    @36
    @20
    @21
    cB
    c.1
    cK
    1cvrjat.b
    1cvrjat.u
    op1cl
    3syl
    cB
    cC
    cK
    @9
    cX
    c.1
    1cvrjat.b
    @27
    1cvrjat.c
    cvrcon3b
    syl3anc
    mpbid
    eqbrtrrd
    @7
    @0
    @30
    @31
    @32
    wa
    wb
    @20
    cA
    cB
    cC
    chlt
    @14
    cK
    @12
    1cvrjat.b
    @34
    1cvrjat.c
    1cvrjat.a
    isat
    syl
    mpbir2and
    cA
    cB
    cC
    @14
    cK
    c.le
    @10
    @12
    1cvrjat.b
    1cvrjat.l
    @34
    1cvrjat.c
    1cvrjat.a
    atcvreq0
    syl3anc
    mpbid
    fveq2d
    @7
    @18
    @19
    @11
    @8
    wceq
    @22
    @26
    cB
    cK
    @9
    @8
    1cvrjat.b
    @27
    opococ
    syl2anc
    @7
    @0
    @18
    @13
    c.1
    wceq
    @20
    @21
    c.1
    cK
    @9
    @12
    @34
    1cvrjat.u
    @27
    opoc0
    3syl
    3eqtr3d
end
