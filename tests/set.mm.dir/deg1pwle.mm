include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "co.mm"
include "cvsca.mm"
include "cle.mm"
include "clmod.mm"
include "cbs.mm"
include "wceq.mm"
include "ply1lmod.mm"
include "adantr.mm"
include "eqid.mm"
include "ply1moncl.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "wbr.mm"
include "simpl.mm"
include "ply1sca.mm"
include "ringidcl.mm"
include "eqeltrrd.mm"
include "simpr.mm"
include "deg1tmle.mm"
include "syl3anc.mm"
include "eqbrtrrd.mm"

theorem deg1pwle
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


  assert |- ( ( R e. Ring /\ F e. NN0 ) -> ( D ` ( F .^ X ) ) <_ F )

  proof
    cR
    crg
    wcel
    #
    cF
    cn0
    wcel
    #
    wa
    #
    cP
    csca
    cfv
    #
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
    @5
    cD
    cfv
    cF
    cle
    @2
    @7
    @5
    cD
    @2
    cP
    clmod
    wcel
    #
    @5
    cP
    cbs
    cfv
    #
    wcel
    @7
    @5
    wceq
    @0
    @9
    @1
    cP
    cR
    deg1pw.p
    ply1lmod
    adantr
    @10
    cF
    cP
    cR
    c.ex
    cN
    cX
    deg1pw.p
    deg1pw.x
    deg1pw.n
    deg1pw.e
    @10
    eqid
    #
    ply1moncl
    @6
    @4
    @3
    @10
    cP
    @5
    @11
    @3
    eqid
    @6
    eqid
    #
    @4
    eqid
    lmodvs1
    syl2anc
    fveq2d
    @2
    @0
    @4
    cR
    cbs
    cfv
    #
    wcel
    #
    @1
    @8
    cF
    cle
    wbr
    @0
    @1
    simpl
    @0
    @14
    @1
    @0
    cR
    cur
    cfv
    #
    @4
    @13
    @0
    cR
    @3
    cur
    cP
    cR
    crg
    deg1pw.p
    ply1sca
    fveq2d
    @13
    cR
    @15
    @13
    eqid
    #
    @15
    eqid
    ringidcl
    eqeltrrd
    adantr
    @0
    @1
    simpr
    @4
    cD
    cP
    cR
    @6
    c.ex
    cF
    @13
    cN
    cX
    deg1pw.d
    @16
    deg1pw.p
    deg1pw.x
    @12
    deg1pw.n
    deg1pw.e
    deg1tmle
    syl3anc
    eqbrtrrd
end
