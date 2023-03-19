include "cn0.mm"
include "cxp.mm"
include "wcel.mm"
include "cfv.mm"
include "cgcd.mm"
include "c2nd.mm"
include "cc0.mm"
include "wceq.mm"
include "cmo.mm"
include "cop.mm"
include "cif.mm"
include "eucalgval.mm"
include "fveq2d.mm"
include "cn.mm"
include "wa.mm"
include "co.mm"
include "c1st.mm"
include "1st2nd2.mm"
include "adantr.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "cz.mm"
include "nnz.mm"
include "adantl.mm"
include "xp1st.mm"
include "nn0zd.mm"
include "zmodcl.mm"
include "sylancom.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "modgcd.mm"
include "3eqtrd.mm"
include "wne.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "3eqtr4d.mm"
include "iftrue.mm"
include "wo.mm"
include "xp2nd.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "eqtrd.mm"

theorem eucalginv
  let vx: setvar x
  let vy: setvar y
  let cE: class E
  let cX: class X
  let cM: class M
  let cN: class N
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume eucalgval.1: |- E = ( x e. NN0 , y e. NN0 |-> if ( y = 0 , <. x , y >. , <. y , ( x mod y ) >. ) )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R z
  disjoint E z
  assert |- ( X e. ( NN0 X. NN0 ) -> ( gcd ` ( E ` X ) ) = ( gcd ` X ) )

  proof
    cX
    cn0
    cn0
    cxp
    wcel
    #
    cX
    cE
    cfv
    #
    cgcd
    cfv
    cX
    c2nd
    cfv
    #
    cc0
    wceq
    #
    cX
    @2
    cX
    cmo
    cfv
    #
    cop
    #
    cif
    #
    cgcd
    cfv
    #
    cX
    cgcd
    cfv
    #
    @0
    @1
    @6
    cgcd
    vx
    vy
    cE
    cX
    eucalgval.1
    eucalgval
    fveq2d
    @0
    @2
    cn
    wcel
    #
    @7
    @8
    wceq
    #
    @3
    @0
    @9
    wa
    #
    @2
    @4
    cgcd
    co
    #
    cX
    c1st
    cfv
    #
    @2
    cgcd
    co
    #
    @7
    @8
    @11
    @12
    @2
    @13
    @2
    cmo
    co
    #
    cgcd
    co
    #
    @15
    @2
    cgcd
    co
    #
    @14
    @11
    @4
    @15
    @2
    cgcd
    @11
    @4
    @13
    @2
    cop
    #
    cmo
    cfv
    @15
    @11
    cX
    @18
    cmo
    @0
    cX
    @18
    wceq
    @9
    cX
    cn0
    cn0
    1st2nd2
    adantr
    #
    fveq2d
    @13
    @2
    cmo
    df-ov
    syl6eqr
    oveq2d
    @11
    @2
    cz
    wcel
    #
    @15
    cz
    wcel
    @16
    @17
    wceq
    @9
    @20
    @0
    @2
    nnz
    adantl
    @11
    @15
    @0
    @9
    @13
    cz
    wcel
    #
    @15
    cn0
    wcel
    @11
    @13
    @0
    @13
    cn0
    wcel
    @9
    cX
    cn0
    cn0
    xp1st
    adantr
    nn0zd
    #
    @13
    @2
    zmodcl
    sylancom
    nn0zd
    @2
    @15
    gcdcom
    syl2anc
    @0
    @9
    @21
    @17
    @14
    wceq
    @22
    @13
    @2
    modgcd
    sylancom
    3eqtrd
    @11
    @7
    @5
    cgcd
    cfv
    @12
    @11
    @6
    @5
    cgcd
    @11
    @3
    cX
    @5
    @11
    @2
    cc0
    @9
    @2
    cc0
    wne
    @0
    @2
    nnne0
    adantl
    neneqd
    iffalsed
    fveq2d
    @2
    @4
    cgcd
    df-ov
    syl6eqr
    @11
    @8
    @18
    cgcd
    cfv
    @14
    @11
    cX
    @18
    cgcd
    @19
    fveq2d
    @13
    @2
    cgcd
    df-ov
    syl6eqr
    3eqtr4d
    @3
    @10
    @0
    @3
    @6
    cX
    cgcd
    @3
    cX
    @5
    iftrue
    fveq2d
    adantl
    @0
    @2
    cn0
    wcel
    @9
    @3
    wo
    cX
    cn0
    cn0
    xp2nd
    @2
    elnn0
    sylib
    mpjaodan
    eqtrd
end
