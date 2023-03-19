include "cnzr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "co.mm"
include "cvsca.mm"
include "csca.mm"
include "wceq.mm"
include "ply1sca.mm"
include "adantr.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "clmod.mm"
include "cbs.mm"
include "crg.mm"
include "nzrring.mm"
include "ply1lmod.mm"
include "syl.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "3syl.mm"
include "simpr.mm"
include "eqid.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "c0g.mm"
include "wne.mm"
include "ringidcl.mm"
include "nzrnz.mm"
include "deg1tm.mm"
include "syl121anc.mm"
include "eqtr3d.mm"

theorem deg1pw
  let cD: class D
  let cP: class P
  let cR: class R
  let c.ex: class .^
  let cF: class F
  let cN: class N
  let cX: class X
  assume deg1pw.d: |- D = ( deg1 ` R )
  assume deg1pw.p: |- P = ( Poly1 ` R )
  assume deg1pw.x: |- X = ( var1 ` R )
  assume deg1pw.n: |- N = ( mulGrp ` P )
  assume deg1pw.e: |- .^ = ( .g ` N )


  assert |- ( ( R e. NzRing /\ F e. NN0 ) -> ( D ` ( F .^ X ) ) = F )

  proof
    cR
    cnzr
    wcel
    #
    cF
    cn0
    wcel
    #
    wa
    #
    cR
    cur
    cfv
    #
    cF
    cX
    c.ex
    co
    #
    cP
    cvsca
    cfv
    #
    co
    #
    cD
    cfv
    #
    @4
    cD
    cfv
    cF
    @2
    @6
    @4
    cD
    @2
    @6
    cP
    csca
    cfv
    #
    cur
    cfv
    #
    @4
    @5
    co
    #
    @4
    @2
    @3
    @9
    @4
    @5
    @2
    cR
    @8
    cur
    @0
    cR
    @8
    wceq
    @1
    cP
    cR
    cnzr
    deg1pw.p
    ply1sca
    adantr
    fveq2d
    oveq1d
    @2
    cP
    clmod
    wcel
    #
    @4
    cP
    cbs
    cfv
    #
    wcel
    #
    @10
    @4
    wceq
    @2
    cR
    crg
    wcel
    #
    @11
    @0
    @14
    @1
    cR
    nzrring
    adantr
    #
    cP
    cR
    deg1pw.p
    ply1lmod
    syl
    @2
    cN
    cmnd
    wcel
    #
    @1
    cX
    @12
    wcel
    #
    @13
    @2
    @14
    cP
    crg
    wcel
    @16
    @15
    cP
    cR
    deg1pw.p
    ply1ring
    cP
    cN
    deg1pw.n
    ringmgp
    3syl
    @0
    @1
    simpr
    #
    @2
    @14
    @17
    @15
    @12
    cP
    cR
    cX
    deg1pw.x
    deg1pw.p
    @12
    eqid
    #
    vr1cl
    syl
    @12
    c.ex
    cN
    cF
    cX
    @12
    cP
    cN
    deg1pw.n
    @19
    mgpbas
    deg1pw.e
    mulgnn0cl
    syl3anc
    @5
    @9
    @8
    @12
    cP
    @4
    @19
    @8
    eqid
    @5
    eqid
    #
    @9
    eqid
    lmodvs1
    syl2anc
    eqtrd
    fveq2d
    @2
    @14
    @3
    cR
    cbs
    cfv
    #
    wcel
    #
    @3
    cR
    c0g
    cfv
    #
    wne
    #
    @1
    @7
    cF
    wceq
    @15
    @2
    @14
    @22
    @15
    @21
    cR
    @3
    @21
    eqid
    #
    @3
    eqid
    #
    ringidcl
    syl
    @0
    @24
    @1
    cR
    @3
    @23
    @26
    @23
    eqid
    #
    nzrnz
    adantr
    @18
    @3
    cD
    cP
    cR
    @5
    c.ex
    cF
    @21
    cN
    cX
    @23
    deg1pw.d
    @25
    deg1pw.p
    deg1pw.x
    @20
    deg1pw.n
    deg1pw.e
    @27
    deg1tm
    syl121anc
    eqtr3d
end
