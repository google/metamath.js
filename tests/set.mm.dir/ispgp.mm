include "cpgp.mm"
include "wbr.mm"
include "cprime.mm"
include "wcel.mm"
include "cgrp.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "cod.mm"
include "cbs.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "simpl.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "rexbidv.mm"
include "raleqbidv.mm"
include "df-pgp.mm"
include "brab2a.mm"
include "df-3an.mm"
include "bitr4i.mm"

theorem ispgp
  let vx: setvar x
  let cP: class P
  let vn: setvar n
  let cG: class G
  let cO: class O
  let cX: class X
  let vg: setvar g
  let vp: setvar p
  assume ispgp.1: |- X = ( Base ` G )
  assume ispgp.2: |- O = ( od ` G )

  disjoint n x
  disjoint G n
  disjoint G x
  disjoint P n
  disjoint P x
  disjoint X x
  disjoint g n
  disjoint g p
  disjoint g x
  disjoint G g
  disjoint n p
  disjoint p x
  disjoint G p
  disjoint O g
  disjoint O p
  disjoint P g
  disjoint P p
  disjoint X g
  disjoint X p
  assert |- ( P pGrp G <-> ( P e. Prime /\ G e. Grp /\ A. x e. X E. n e. NN0 ( O ` x ) = ( P ^ n ) ) )

  proof
    cP
    cG
    cpgp
    wbr
    cP
    cprime
    wcel
    #
    cG
    cgrp
    wcel
    #
    wa
    vx
    cv
    #
    cO
    cfv
    #
    cP
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    vx
    cX
    wral
    #
    wa
    @0
    @1
    @8
    w3a
    @2
    vg
    cv
    #
    cod
    cfv
    #
    cfv
    #
    vp
    cv
    #
    @4
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    vx
    @9
    cbs
    cfv
    #
    wral
    @8
    vp
    vg
    cP
    cG
    cprime
    cgrp
    cpgp
    @12
    cP
    wceq
    #
    @9
    cG
    wceq
    #
    wa
    #
    @15
    @7
    vx
    @16
    cX
    @19
    @16
    cG
    cbs
    cfv
    cX
    @19
    @9
    cG
    cbs
    @17
    @18
    simpr
    #
    fveq2d
    ispgp.1
    syl6eqr
    @19
    @14
    @6
    vn
    cn0
    @19
    @11
    @3
    @13
    @5
    @19
    @2
    @10
    cO
    @19
    @10
    cG
    cod
    cfv
    cO
    @19
    @9
    cG
    cod
    @20
    fveq2d
    ispgp.2
    syl6eqr
    fveq1d
    @19
    @12
    cP
    @4
    cexp
    @17
    @18
    simpl
    oveq1d
    eqeq12d
    rexbidv
    raleqbidv
    vx
    vg
    vn
    vp
    df-pgp
    brab2a
    @0
    @1
    @8
    df-3an
    bitr4i
end
