include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "cmgp.mm"
include "ccom.mm"
include "cplusg.mm"
include "cvv.mm"
include "eqid.mm"
include "simpr.mm"
include "fvexd.mm"
include "wfn.mm"
include "fnconstg.mm"
include "adantr.mm"
include "prdsmgp.mm"
include "simpld.mm"
include "pwsval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cpws.mm"
include "fvex.mm"
include "eqeltri.mm"
include "sylancr.mm"
include "mgpsca.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fnmgp.mm"
include "elex.mm"
include "fcoconst.mm"
include "sneqi.mm"
include "xpeq2i.mm"
include "syl6reqr.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "3eqtr4g.mm"
include "simprd.mm"
include "jca.mm"

theorem pwsmgp
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume pwsmgp.y: |- Y = ( R ^s I )
  assume pwsmgp.m: |- M = ( mulGrp ` R )
  assume pwsmgp.z: |- Z = ( M ^s I )
  assume pwsmgp.n: |- N = ( mulGrp ` Y )
  assume pwsmgp.b: |- B = ( Base ` N )
  assume pwsmgp.c: |- C = ( Base ` Z )
  assume pwsmgp.p: |- .+ = ( +g ` N )
  assume pwsmgp.q: |- .+b = ( +g ` Z )


  assert |- ( ( R e. V /\ I e. W ) -> ( B = C /\ .+ = .+b ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cB
    cC
    wceq
    c.pl
    c.pb
    wceq
    @2
    cN
    cbs
    cfv
    #
    cZ
    cbs
    cfv
    #
    cB
    cC
    @2
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    cmgp
    cfv
    #
    cbs
    cfv
    #
    @5
    cmgp
    @6
    ccom
    #
    cprds
    co
    #
    cbs
    cfv
    #
    @3
    @4
    @2
    @9
    @12
    wceq
    #
    @8
    cplusg
    cfv
    #
    @11
    cplusg
    cfv
    #
    wceq
    #
    @2
    @6
    @5
    cI
    @8
    cW
    cvv
    @7
    @11
    @7
    eqid
    @8
    eqid
    @11
    eqid
    @0
    @1
    simpr
    #
    @2
    cR
    csca
    fvexd
    @0
    @6
    cI
    wfn
    @1
    cI
    cR
    cV
    fnconstg
    adantr
    prdsmgp
    #
    simpld
    @2
    cN
    @8
    cbs
    @2
    cN
    cY
    cmgp
    cfv
    @8
    pwsmgp.n
    @2
    cY
    @7
    cmgp
    cR
    @5
    cI
    cV
    cW
    cY
    pwsmgp.y
    @5
    eqid
    #
    pwsval
    fveq2d
    syl5eq
    #
    fveq2d
    @2
    cZ
    @11
    cbs
    @2
    cZ
    cM
    cI
    cpws
    co
    #
    @11
    pwsmgp.z
    @2
    @21
    cM
    csca
    cfv
    #
    cI
    cM
    csn
    #
    cxp
    #
    cprds
    co
    #
    @11
    @2
    cM
    cvv
    wcel
    @1
    @21
    @25
    wceq
    cM
    cR
    cmgp
    cfv
    #
    cvv
    pwsmgp.m
    cR
    cmgp
    fvex
    eqeltri
    @17
    cM
    @22
    cI
    cvv
    cW
    @21
    @21
    eqid
    @22
    eqid
    pwsval
    sylancr
    @2
    @22
    @5
    @24
    @10
    cprds
    @22
    @5
    wceq
    @2
    @5
    @22
    cR
    @5
    cM
    pwsmgp.m
    @19
    mgpsca
    eqcomi
    a1i
    @2
    @10
    cI
    @26
    csn
    #
    cxp
    #
    @24
    @2
    cmgp
    cvv
    wfn
    cR
    cvv
    wcel
    #
    @10
    @28
    wceq
    fnmgp
    @0
    @29
    @1
    cR
    cV
    elex
    adantr
    cmgp
    cI
    cvv
    cR
    fcoconst
    sylancr
    @23
    @27
    cI
    cM
    @26
    pwsmgp.m
    sneqi
    xpeq2i
    syl6reqr
    oveq12d
    eqtrd
    syl5eq
    #
    fveq2d
    3eqtr4d
    pwsmgp.b
    pwsmgp.c
    3eqtr4g
    @2
    cN
    cplusg
    cfv
    #
    cZ
    cplusg
    cfv
    #
    c.pl
    c.pb
    @2
    @14
    @15
    @31
    @32
    @2
    @13
    @16
    @18
    simprd
    @2
    cN
    @8
    cplusg
    @20
    fveq2d
    @2
    cZ
    @11
    cplusg
    @30
    fveq2d
    3eqtr4d
    pwsmgp.p
    pwsmgp.q
    3eqtr4g
    jca
end
