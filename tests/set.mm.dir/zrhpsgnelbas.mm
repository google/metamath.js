include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "crg.mm"
include "cfn.mm"
include "w3a.mm"
include "cbs.mm"
include "psgnran.mm"
include "3adant1.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "cur.mm"
include "eqid.mm"
include "zrh1.mm"
include "ringidcl.mm"
include "eqeltrd.mm"
include "3ad2ant1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "cmg.mm"
include "co.mm"
include "cz.mm"
include "neg1z.mm"
include "zrhmulg.mm"
include "mpan2.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "a1i.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "jaoi.mm"
include "syl.mm"
include "mpcom.mm"

theorem zrhpsgnelbas
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cN: class N
  let cY: class Y
  assume zrhpsgnelbas.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume zrhpsgnelbas.s: |- S = ( pmSgn ` N )
  assume zrhpsgnelbas.y: |- Y = ( ZRHom ` R )


  assert |- ( ( R e. Ring /\ N e. Fin /\ Q e. P ) -> ( Y ` ( S ` Q ) ) e. ( Base ` R ) )

  proof
    cQ
    cS
    cfv
    #
    c1
    c1
    cneg
    #
    cpr
    wcel
    #
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    cQ
    cP
    wcel
    #
    w3a
    #
    @0
    cY
    cfv
    #
    cR
    cbs
    cfv
    #
    wcel
    #
    @4
    @5
    @2
    @3
    cP
    cQ
    cS
    cN
    zrhpsgnelbas.p
    zrhpsgnelbas.s
    psgnran
    3adant1
    @2
    @0
    c1
    wceq
    #
    @0
    @1
    wceq
    #
    wo
    @6
    @9
    wi
    #
    @0
    c1
    @1
    elpri
    @10
    @12
    @11
    @6
    @9
    @10
    c1
    cY
    cfv
    #
    @8
    wcel
    #
    @3
    @4
    @14
    @5
    @3
    @13
    cR
    cur
    cfv
    #
    @8
    cR
    @15
    cY
    zrhpsgnelbas.y
    @15
    eqid
    #
    zrh1
    @8
    cR
    @15
    @8
    eqid
    #
    @16
    ringidcl
    #
    eqeltrd
    3ad2ant1
    @10
    @7
    @13
    @8
    @0
    c1
    cY
    fveq2
    eleq1d
    syl5ibr
    @6
    @9
    @11
    @1
    cY
    cfv
    #
    @8
    wcel
    #
    @3
    @4
    @20
    @5
    @3
    @19
    @1
    @15
    cR
    cmg
    cfv
    #
    co
    #
    @8
    @3
    @1
    cz
    wcel
    #
    @19
    @22
    wceq
    neg1z
    cR
    @21
    @15
    cY
    @1
    zrhpsgnelbas.y
    @21
    eqid
    #
    @16
    zrhmulg
    mpan2
    @3
    cR
    cgrp
    wcel
    @23
    @15
    @8
    wcel
    @22
    @8
    wcel
    cR
    ringgrp
    @23
    @3
    neg1z
    a1i
    @18
    @8
    @21
    cR
    @1
    @15
    @17
    @24
    mulgcl
    syl3anc
    eqeltrd
    3ad2ant1
    @11
    @7
    @19
    @8
    @0
    @1
    cY
    fveq2
    eleq1d
    syl5ibr
    jaoi
    syl
    mpcom
end
