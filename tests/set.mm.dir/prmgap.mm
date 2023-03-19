include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cprime.mm"
include "wnel.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cn.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "cmpt.mm"
include "id.mm"
include "cmap.mm"
include "facmapnn.mm"
include "a1i.mm"
include "cgcd.mm"
include "clt.mm"
include "c2.mm"
include "cfz.mm"
include "prmgaplem2.mm"
include "cvv.mm"
include "eqidd.mm"
include "wceq.mm"
include "fveq2.mm"
include "adantl.mm"
include "simpl.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "prmgaplem8.mm"
include "rgen.mm"

theorem prmgap
  let vz: setvar z
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let vi: setvar i
  let vx: setvar x

  disjoint n p
  disjoint n q
  disjoint n z
  disjoint p q
  disjoint p z
  disjoint q z
  disjoint i n
  disjoint i p
  disjoint i q
  disjoint i x
  disjoint i z
  disjoint n x
  disjoint p x
  disjoint q x
  disjoint x z
  assert |- A. n e. NN E. p e. Prime E. q e. Prime ( n <_ ( q - p ) /\ A. z e. ( ( p + 1 ) ..^ q ) z e/ Prime )

  proof
    vn
    cv
    #
    vq
    cv
    #
    vp
    cv
    #
    cmin
    co
    cle
    wbr
    vz
    cv
    cprime
    wnel
    vz
    @2
    c1
    caddc
    co
    @1
    cfzo
    co
    wral
    wa
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    vn
    cn
    @0
    cn
    wcel
    #
    vz
    vi
    vx
    cn
    vx
    cv
    #
    cfa
    cfv
    #
    cmpt
    #
    @0
    vq
    vp
    @3
    id
    @6
    cn
    cn
    cmap
    co
    wcel
    @3
    vx
    facmapnn
    a1i
    @3
    c1
    @0
    @6
    cfv
    #
    vi
    cv
    #
    caddc
    co
    #
    @8
    cgcd
    co
    #
    clt
    wbr
    vi
    c2
    @0
    cfz
    co
    #
    @3
    @8
    @11
    wcel
    #
    wa
    #
    c1
    @0
    cfa
    cfv
    #
    @8
    caddc
    co
    #
    @8
    cgcd
    co
    @10
    clt
    @8
    @0
    prmgaplem2
    @13
    @9
    @15
    @8
    cgcd
    @13
    @7
    @14
    @8
    caddc
    @13
    vx
    @0
    @5
    @14
    cn
    @6
    cvv
    @13
    @6
    eqidd
    @4
    @0
    wceq
    @5
    @14
    wceq
    @13
    @4
    @0
    cfa
    fveq2
    adantl
    @3
    @12
    simpl
    @13
    @0
    cfa
    fvexd
    fvmptd
    oveq1d
    oveq1d
    breqtrrd
    ralrimiva
    prmgaplem8
    rgen
end
