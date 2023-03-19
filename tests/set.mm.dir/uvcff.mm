include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "cbs.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "ad3antrrr.mm"
include "fmptd.mm"
include "wb.mm"
include "cvv.mm"
include "fvex.mm"
include "elmapg.mm"
include "mpan.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "wfun.mm"
include "csn.mm"
include "cfn.mm"
include "csupp.mm"
include "wss.mm"
include "mptexg.mm"
include "funmpt.mm"
include "a1i.mm"
include "snfi.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "simplr.mm"
include "suppss2.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "frlmelbas.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "uvcfval.mm"
include "feq1d.mm"

theorem uvcff
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cW: class W
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  assume uvcff.u: |- U = ( R unitVec I )
  assume uvcff.y: |- Y = ( R freeLMod I )
  assume uvcff.b: |- B = ( Base ` Y )


  assert |- ( ( R e. Ring /\ I e. W ) -> U : I --> B )

  proof
    cR
    crg
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cI
    cB
    cU
    wf
    cI
    cB
    vi
    cI
    vj
    cI
    vj
    cv
    #
    vi
    cv
    #
    wceq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    wf
    @2
    vi
    cI
    @9
    cB
    @10
    @2
    @4
    cI
    wcel
    #
    wa
    #
    @9
    cB
    wcel
    #
    @9
    cR
    cbs
    cfv
    #
    cI
    cmap
    co
    wcel
    #
    @9
    @7
    cfsupp
    wbr
    #
    @12
    @15
    cI
    @14
    @9
    wf
    #
    @12
    vj
    cI
    @8
    @14
    @9
    @0
    @8
    @14
    wcel
    @1
    @11
    @3
    cI
    wcel
    @0
    @5
    @6
    @7
    @14
    @14
    cR
    @6
    @14
    eqid
    #
    @6
    eqid
    #
    ringidcl
    @14
    cR
    @7
    @18
    @7
    eqid
    #
    ring0cl
    ifcld
    ad3antrrr
    @9
    eqid
    fmptd
    @1
    @15
    @17
    wb
    #
    @0
    @11
    @14
    cvv
    wcel
    @1
    @21
    cR
    cbs
    fvex
    @14
    cI
    @9
    cvv
    cW
    elmapg
    mpan
    ad2antlr
    mpbird
    @12
    @9
    cvv
    wcel
    #
    @9
    wfun
    #
    @7
    cvv
    wcel
    #
    @4
    csn
    #
    cfn
    wcel
    #
    @9
    @7
    csupp
    co
    @25
    wss
    @16
    @1
    @22
    @0
    @11
    vj
    cI
    @8
    cW
    mptexg
    ad2antlr
    @23
    @12
    vj
    cI
    @8
    funmpt
    a1i
    @24
    @12
    cR
    c0g
    fvex
    a1i
    @26
    @12
    @4
    snfi
    a1i
    @12
    cI
    @8
    vj
    cW
    @25
    @7
    @12
    @3
    cI
    @25
    cdif
    wcel
    #
    wa
    #
    @5
    @6
    @7
    @28
    @3
    @4
    @27
    @3
    @4
    wne
    @12
    @3
    cI
    @4
    eldifsni
    adantl
    neneqd
    iffalsed
    @0
    @1
    @11
    simplr
    suppss2
    @25
    @9
    cvv
    cvv
    @7
    suppssfifsupp
    syl32anc
    @2
    @13
    @15
    @16
    wa
    wb
    @11
    cB
    cR
    cY
    cI
    @14
    crg
    cW
    @9
    @7
    uvcff.y
    @18
    @20
    uvcff.b
    frlmelbas
    adantr
    mpbir2and
    @10
    eqid
    fmptd
    @2
    cI
    cB
    cU
    @10
    cR
    cU
    @6
    vi
    vj
    cI
    crg
    cW
    @7
    uvcff.u
    @19
    @20
    uvcfval
    feq1d
    mpbird
end
