include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "symgfixf.mm"
include "adantl.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cif.mm"
include "cmpt.mm"
include "weq.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "symgfixfolem1.mm"
include "3expa.mm"
include "wi.mm"
include "simpr.mm"
include "anim1i.mm"
include "eqid.mm"
include "symgextres.mm"
include "syl.mm"
include "eqcomd.mm"
include "wb.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "rspcimedv.mm"
include "pm2.43i.mm"
include "fvtresfn.mm"
include "rexbidva.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem symgfixfo
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let vq: setvar q
  let vg: setvar g
  let vp: setvar p
  let vi: setvar i
  let vs: setvar s
  let vj: setvar j
  assume symgfixf.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgfixf.q: |- Q = { q e. P | ( q ` K ) = K }
  assume symgfixf.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgfixf.h: |- H = ( q e. Q |-> ( q |` ( N \ { K } ) ) )

  disjoint K q
  disjoint P q
  disjoint N q
  disjoint Q q
  disjoint S q
  disjoint H g
  disjoint H p
  disjoint g p
  disjoint K g
  disjoint K i
  disjoint K p
  disjoint g i
  disjoint i p
  disjoint N g
  disjoint N i
  disjoint N p
  disjoint g q
  disjoint i q
  disjoint p q
  disjoint Q g
  disjoint Q p
  disjoint H s
  disjoint K s
  disjoint N s
  disjoint Q s
  disjoint S p
  disjoint S s
  disjoint p s
  disjoint S i
  disjoint S j
  disjoint i j
  disjoint i s
  disjoint j s
  disjoint V p
  disjoint V j
  disjoint V s
  disjoint K j
  disjoint N j
  assert |- ( ( N e. V /\ K e. N ) -> H : Q -onto-> S )

  proof
    cN
    cV
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cQ
    cS
    cH
    wf
    #
    vs
    cv
    #
    vp
    cv
    #
    cH
    cfv
    #
    wceq
    #
    vp
    cQ
    wrex
    #
    vs
    cS
    wral
    cQ
    cS
    cH
    wfo
    @1
    @3
    @0
    cP
    cQ
    cS
    cH
    cK
    cN
    vq
    symgfixf.p
    symgfixf.q
    symgfixf.s
    symgfixf.h
    symgfixf
    adantl
    @2
    @8
    vs
    cS
    @2
    @4
    cS
    wcel
    #
    wa
    #
    @8
    @4
    @5
    cN
    cK
    csn
    cdif
    #
    cres
    #
    wceq
    #
    vp
    cQ
    wrex
    #
    @10
    @14
    @10
    @13
    @10
    vp
    vi
    cN
    vi
    cv
    #
    cK
    wceq
    #
    cK
    @15
    @4
    cfv
    #
    cif
    #
    cmpt
    #
    cQ
    @0
    @1
    @9
    @19
    cQ
    wcel
    vj
    cP
    cQ
    cS
    @19
    cH
    cK
    cN
    cV
    @4
    vq
    symgfixf.p
    symgfixf.q
    symgfixf.s
    symgfixf.h
    vi
    vj
    cN
    @18
    vj
    cv
    #
    cK
    wceq
    #
    cK
    @20
    @4
    cfv
    #
    cif
    vi
    vj
    weq
    @16
    @21
    @17
    @22
    cK
    @15
    @20
    cK
    eqeq1
    @15
    @20
    @4
    fveq2
    ifbieq2d
    cbvmptv
    symgfixfolem1
    3expa
    @5
    @19
    wceq
    #
    @10
    @13
    wi
    @10
    @23
    @10
    @13
    @23
    @10
    wa
    #
    @13
    @4
    @19
    @11
    cres
    #
    wceq
    #
    @24
    @25
    @4
    @24
    @1
    @9
    wa
    #
    @25
    @4
    wceq
    @10
    @27
    @23
    @2
    @1
    @9
    @0
    @1
    simpr
    anim1i
    adantl
    vi
    cS
    @19
    cK
    cN
    @4
    symgfixf.s
    @19
    eqid
    symgextres
    syl
    eqcomd
    @23
    @13
    @26
    wb
    @10
    @23
    @12
    @25
    @4
    @5
    @19
    @11
    reseq1
    eqeq2d
    adantr
    mpbird
    ex
    adantl
    rspcimedv
    pm2.43i
    @10
    @7
    @13
    vp
    cQ
    @5
    cQ
    wcel
    #
    @7
    @13
    wb
    @10
    @28
    @6
    @12
    @4
    vq
    cQ
    cH
    @11
    @5
    symgfixf.h
    fvtresfn
    eqeq2d
    adantl
    rexbidva
    mpbird
    ralrimiva
    vp
    vs
    cQ
    cS
    cH
    dffo3
    sylanbrc
end
