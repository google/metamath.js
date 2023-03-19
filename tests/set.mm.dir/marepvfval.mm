include "cmatrepV.mm"
include "co.mm"
include "weq.mm"
include "cv.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cmap.mm"
include "ovex.mm"
include "a1i.mm"
include "mpt2exga.mm"
include "sylancr.mm"
include "cmat.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "adantl.mm"
include "simpl.mm"
include "oveq12d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "mpteq12dv.mm"
include "df-marepv.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "mpt20.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "matbas0pc.mm"
include "syl5eq.mm"
include "mpt2eq12.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem marepvfval
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vr: setvar r
  assume marepvfval.a: |- A = ( N Mat R )
  assume marepvfval.b: |- B = ( Base ` A )
  assume marepvfval.q: |- Q = ( N matRepV R )
  assume marepvfval.v: |- V = ( ( Base ` R ) ^m N )

  disjoint B m
  disjoint B v
  disjoint m v
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N m
  disjoint N v
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i v
  disjoint j k
  disjoint j m
  disjoint j v
  disjoint k m
  disjoint k v
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R v
  disjoint V m
  disjoint V v
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint n v
  disjoint r v
  disjoint N n
  disjoint N r
  disjoint i n
  disjoint i r
  disjoint j n
  disjoint j r
  disjoint k n
  disjoint k r
  disjoint R n
  disjoint R r
  disjoint V n
  disjoint V r
  assert |- Q = ( m e. B , v e. V |-> ( k e. N |-> ( i e. N , j e. N |-> if ( j = k , ( v ` i ) , ( i m j ) ) ) ) )

  proof
    cQ
    cN
    cR
    cmatrepV
    co
    #
    vm
    vv
    cB
    cV
    vk
    cN
    vi
    vj
    cN
    cN
    vj
    vk
    weq
    vi
    cv
    #
    vv
    cv
    cfv
    @1
    vj
    cv
    vm
    cv
    co
    cif
    #
    cmpt2
    #
    cmpt
    #
    cmpt2
    #
    marepvfval.q
    cN
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    @0
    @5
    wceq
    #
    @6
    @7
    @5
    cvv
    wcel
    #
    @9
    @8
    cB
    cvv
    wcel
    cV
    cvv
    wcel
    #
    @10
    cB
    cA
    cbs
    cfv
    #
    cvv
    marepvfval.b
    cA
    cbs
    fvex
    eqeltri
    @11
    @8
    cV
    cR
    cbs
    cfv
    #
    cN
    cmap
    co
    #
    cvv
    marepvfval.v
    @13
    cN
    cmap
    ovex
    eqeltri
    a1i
    vm
    vv
    cB
    cV
    @4
    cvv
    cvv
    mpt2exga
    sylancr
    vn
    vr
    cN
    cR
    cvv
    cvv
    vm
    vv
    vn
    cv
    #
    vr
    cv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    @16
    cbs
    cfv
    #
    @15
    cmap
    co
    #
    vk
    @15
    vi
    vj
    @15
    @15
    @2
    cmpt2
    #
    cmpt
    #
    cmpt2
    #
    @5
    cmatrepV
    cvv
    @15
    cN
    wceq
    #
    @16
    cR
    wceq
    #
    wa
    #
    vm
    vv
    @18
    @20
    @22
    cB
    cV
    @4
    @26
    @18
    @12
    cB
    @26
    @17
    cA
    cbs
    @26
    @17
    cN
    cR
    cmat
    co
    #
    cA
    @15
    cN
    @16
    cR
    cmat
    oveq12
    marepvfval.a
    syl6eqr
    fveq2d
    marepvfval.b
    syl6eqr
    @26
    @20
    @14
    cV
    @26
    @19
    @13
    @15
    cN
    cmap
    @25
    @19
    @13
    wceq
    @24
    @16
    cR
    cbs
    fveq2
    adantl
    @24
    @25
    simpl
    #
    oveq12d
    marepvfval.v
    syl6eqr
    @26
    vk
    @15
    @21
    cN
    @3
    @28
    @26
    vi
    vj
    @15
    @15
    @2
    cN
    cN
    @2
    @28
    @28
    @26
    @2
    eqidd
    mpt2eq123dv
    mpteq12dv
    mpt2eq123dv
    vv
    vi
    vj
    vk
    vm
    vn
    vr
    df-marepv
    #
    ovmpt2ga
    mpd3an3
    @8
    wn
    #
    @0
    vm
    vv
    c0
    @14
    @4
    cmpt2
    #
    @5
    @30
    @0
    c0
    @31
    vn
    vr
    @23
    cmatrepV
    cN
    cR
    cvv
    cvv
    @29
    mpt2ndm0
    vm
    vv
    @14
    @4
    mpt20
    syl6eqr
    @30
    cB
    c0
    wceq
    cV
    @14
    wceq
    @5
    @31
    wceq
    @30
    cB
    @27
    cbs
    cfv
    #
    c0
    cB
    @12
    @32
    marepvfval.b
    cA
    @27
    cbs
    marepvfval.a
    fveq2i
    eqtri
    cR
    cN
    matbas0pc
    syl5eq
    marepvfval.v
    vm
    vv
    cB
    cV
    c0
    @14
    @4
    mpt2eq12
    sylancl
    eqtr4d
    pm2.61i
    eqtri
end
