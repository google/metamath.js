include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "cmgp.mm"
include "wceq.mm"
include "cvv.mm"
include "simpr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "simplr.mm"
include "eqid.mm"
include "mgpbas.mm"
include "ressid2.mm"
include "syl3anc.mm"
include "simpll.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "wn.mm"
include "cnx.mm"
include "cin.mm"
include "cop.mm"
include "csts.mm"
include "cplusg.mm"
include "cmulr.mm"
include "mgpval.mm"
include "oveq1i.mm"
include "ressval2.mm"
include "ressmulr.mm"
include "eqcomd.mm"
include "ad2antlr.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "wne.mm"
include "c2.mm"
include "c1.mm"
include "1ne2.mm"
include "necomi.mm"
include "plusgndx.mm"
include "basendx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "inex2.mm"
include "setscom.mm"
include "mpanr12.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem mgpress
  let cA: class A
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let cW: class W
  assume mgpress.1: |- S = ( R |`s A )
  assume mgpress.2: |- M = ( mulGrp ` R )


  assert |- ( ( R e. V /\ A e. W ) -> ( M |`s A ) = ( mulGrp ` S ) )

  proof
    cR
    cV
    wcel
    #
    cA
    cW
    wcel
    #
    wa
    #
    cR
    cbs
    cfv
    #
    cA
    wss
    #
    cM
    cA
    cress
    co
    #
    cS
    cmgp
    cfv
    #
    wceq
    @2
    @4
    wa
    #
    cM
    cR
    cmgp
    cfv
    #
    @5
    @6
    mgpress.2
    @7
    @4
    cM
    cvv
    wcel
    #
    @1
    @5
    cM
    wceq
    @2
    @4
    simpr
    #
    @9
    @7
    cM
    @8
    cvv
    mgpress.2
    cR
    cmgp
    fvex
    eqeltri
    #
    a1i
    @0
    @1
    @4
    simplr
    #
    cA
    @3
    @5
    cM
    cvv
    cW
    @5
    eqid
    #
    @3
    cR
    cM
    mgpress.2
    @3
    eqid
    #
    mgpbas
    #
    ressid2
    syl3anc
    @7
    cS
    cR
    cmgp
    @7
    @4
    @0
    @1
    cS
    cR
    wceq
    @10
    @0
    @1
    @4
    simpll
    @12
    cA
    @3
    cS
    cR
    cV
    cW
    mgpress.1
    @14
    ressid2
    syl3anc
    fveq2d
    3eqtr4a
    @2
    @4
    wn
    #
    wa
    #
    cM
    cnx
    cbs
    cfv
    #
    cA
    @3
    cin
    #
    cop
    #
    csts
    co
    #
    cR
    cnx
    cplusg
    cfv
    #
    cR
    cmulr
    cfv
    #
    cop
    #
    csts
    co
    #
    @20
    csts
    co
    #
    @5
    @6
    cM
    @25
    @20
    csts
    cR
    @23
    cM
    mgpress.2
    @23
    eqid
    #
    mgpval
    oveq1i
    @17
    @16
    @9
    @1
    @5
    @21
    wceq
    @2
    @16
    simpr
    #
    @9
    @17
    @11
    a1i
    @0
    @1
    @16
    simplr
    #
    cA
    @3
    @5
    cM
    cvv
    cW
    @13
    @15
    ressval2
    syl3anc
    @17
    @6
    cR
    @20
    csts
    co
    #
    @24
    csts
    co
    #
    @26
    @17
    @6
    cS
    @22
    cS
    cmulr
    cfv
    #
    cop
    #
    csts
    co
    @31
    cS
    @32
    @6
    @6
    eqid
    @32
    eqid
    mgpval
    @17
    cS
    @30
    @33
    @24
    csts
    @17
    @16
    @0
    @1
    cS
    @30
    wceq
    @28
    @0
    @1
    @16
    simpll
    #
    @29
    cA
    @3
    cS
    cR
    cV
    cW
    mgpress.1
    @14
    ressval2
    syl3anc
    @17
    @32
    @23
    @22
    @1
    @32
    @23
    wceq
    @0
    @16
    @1
    @23
    @32
    cA
    cR
    cS
    @23
    cW
    mgpress.1
    @27
    ressmulr
    eqcomd
    ad2antlr
    opeq2d
    oveq12d
    syl5eq
    @17
    @0
    @22
    @18
    wne
    #
    @26
    @31
    wceq
    #
    @34
    @35
    c2
    c1
    wne
    c1
    c2
    1ne2
    necomi
    @22
    c2
    @18
    c1
    plusgndx
    basendx
    neeq12i
    mpbir
    @0
    @35
    wa
    @23
    cvv
    wcel
    @19
    cvv
    wcel
    @36
    cR
    cmulr
    fvex
    @3
    cA
    cR
    cbs
    fvex
    inex2
    @22
    @18
    @23
    @19
    cR
    cV
    cvv
    cvv
    cnx
    cplusg
    fvex
    cnx
    cbs
    fvex
    setscom
    mpanr12
    sylancl
    eqtr4d
    3eqtr4a
    pm2.61dan
end
