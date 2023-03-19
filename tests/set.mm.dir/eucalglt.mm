include "cn0.mm"
include "cxp.mm"
include "wcel.mm"
include "cfv.mm"
include "c2nd.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1st.mm"
include "cmo.mm"
include "co.mm"
include "cop.mm"
include "wceq.mm"
include "cif.mm"
include "eucalgval.mm"
include "adantr.mm"
include "wn.mm"
include "simpr.mm"
include "iftrue.mm"
include "eqeq2d.mm"
include "fveq2.mm"
include "syl6bi.mm"
include "eqeq2.mm"
include "sylibd.mm"
include "syl5com.mm"
include "necon3ad.mm"
include "mpd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "fvex.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "1st2nd2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "cr.mm"
include "crp.mm"
include "xp1st.mm"
include "nn0red.mm"
include "cn.mm"
include "wo.mm"
include "xp2nd.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "nnrpd.mm"
include "modlt.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "ex.mm"

theorem eucalglt
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
  assert |- ( X e. ( NN0 X. NN0 ) -> ( ( 2nd ` ( E ` X ) ) =/= 0 -> ( 2nd ` ( E ` X ) ) < ( 2nd ` X ) ) )

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
    c2nd
    cfv
    #
    cc0
    wne
    #
    @2
    cX
    c2nd
    cfv
    #
    clt
    wbr
    @0
    @3
    wa
    #
    @2
    cX
    c1st
    cfv
    #
    @4
    cmo
    co
    #
    @4
    clt
    @5
    @2
    cX
    cmo
    cfv
    #
    @7
    @5
    @2
    @4
    @8
    cop
    #
    c2nd
    cfv
    @8
    @5
    @1
    @9
    c2nd
    @5
    @1
    @4
    cc0
    wceq
    #
    cX
    @9
    cif
    #
    @9
    @0
    @1
    @11
    wceq
    #
    @3
    vx
    vy
    cE
    cX
    eucalgval.1
    eucalgval
    adantr
    #
    @5
    @10
    cX
    @9
    @5
    @3
    @10
    wn
    @0
    @3
    simpr
    @5
    @10
    @2
    cc0
    @5
    @12
    @10
    @2
    cc0
    wceq
    #
    @13
    @10
    @12
    @2
    @4
    wceq
    #
    @14
    @10
    @12
    @1
    cX
    wceq
    @15
    @10
    @11
    cX
    @1
    @10
    cX
    @9
    iftrue
    eqeq2d
    @1
    cX
    c2nd
    fveq2
    syl6bi
    @4
    cc0
    @2
    eqeq2
    sylibd
    syl5com
    necon3ad
    mpd
    #
    iffalsed
    eqtrd
    fveq2d
    @4
    @8
    cX
    c2nd
    fvex
    cX
    cmo
    fvex
    op2nd
    syl6eq
    @5
    @8
    @6
    @4
    cop
    #
    cmo
    cfv
    @7
    @5
    cX
    @17
    cmo
    @0
    cX
    @17
    wceq
    @3
    cX
    cn0
    cn0
    1st2nd2
    adantr
    fveq2d
    @6
    @4
    cmo
    df-ov
    syl6eqr
    eqtrd
    @5
    @6
    cr
    wcel
    @4
    crp
    wcel
    @7
    @4
    clt
    wbr
    @5
    @6
    @0
    @6
    cn0
    wcel
    @3
    cX
    cn0
    cn0
    xp1st
    adantr
    nn0red
    @5
    @4
    @5
    @4
    cn
    wcel
    #
    @10
    @16
    @5
    @18
    @10
    @5
    @4
    cn0
    wcel
    #
    @18
    @10
    wo
    @0
    @19
    @3
    cX
    cn0
    cn0
    xp2nd
    adantr
    @4
    elnn0
    sylib
    ord
    mt3d
    nnrpd
    @6
    @4
    modlt
    syl2anc
    eqbrtrd
    ex
end
