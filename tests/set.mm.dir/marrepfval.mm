include "cmarrep.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "weq.mm"
include "cv.mm"
include "cif.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvexd.mm"
include "mpt2exga.mm"
include "sylancr.mm"
include "cmat.mm"
include "c0g.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "fveq2.mm"
include "adantl.mm"
include "simpl.mm"
include "ifeq2d.mm"
include "ifeq1d.mm"
include "mpt2eq123dv.mm"
include "df-marrep.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "mpt20.mm"
include "matbas0pc.mm"
include "syl5eq.mm"
include "eqidd.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem marrepfval
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let c.0: class .0.
  let vs: setvar s
  let vl: setvar l
  let vn: setvar n
  let vr: setvar r
  assume marrepfval.a: |- A = ( N Mat R )
  assume marrepfval.b: |- B = ( Base ` A )
  assume marrepfval.q: |- Q = ( N matRRep R )
  assume marrepfval.z: |- .0. = ( 0g ` R )

  disjoint B m
  disjoint B s
  disjoint m s
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint N s
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i s
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j s
  disjoint k l
  disjoint k m
  disjoint k s
  disjoint l m
  disjoint l s
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint R m
  disjoint R s
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint n s
  disjoint r s
  disjoint N n
  disjoint N r
  disjoint i n
  disjoint i r
  disjoint j n
  disjoint j r
  disjoint k n
  disjoint k r
  disjoint l n
  disjoint l r
  disjoint R n
  disjoint R r
  disjoint .0. n
  disjoint .0. r
  assert |- Q = ( m e. B , s e. ( Base ` R ) |-> ( k e. N , l e. N |-> ( i e. N , j e. N |-> if ( i = k , if ( j = l , s , .0. ) , ( i m j ) ) ) ) )

  proof
    cQ
    cN
    cR
    cmarrep
    co
    #
    vm
    vs
    cB
    cR
    cbs
    cfv
    #
    vk
    vl
    cN
    cN
    vi
    vj
    cN
    cN
    vi
    vk
    weq
    #
    vj
    vl
    weq
    #
    vs
    cv
    #
    c.0
    cif
    #
    vi
    cv
    vj
    cv
    vm
    cv
    co
    #
    cif
    #
    cmpt2
    #
    cmpt2
    #
    cmpt2
    #
    marrepfval.q
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
    @10
    wceq
    #
    @11
    @12
    @10
    cvv
    wcel
    #
    @14
    @13
    cB
    cvv
    wcel
    @1
    cvv
    wcel
    @15
    cB
    cA
    cbs
    cfv
    #
    cvv
    marrepfval.b
    cA
    cbs
    fvex
    eqeltri
    @13
    cR
    cbs
    fvexd
    vm
    vs
    cB
    @1
    @9
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
    vs
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
    @18
    cbs
    cfv
    #
    vk
    vl
    @17
    @17
    vi
    vj
    @17
    @17
    @2
    @3
    @4
    @18
    c0g
    cfv
    #
    cif
    #
    @6
    cif
    #
    cmpt2
    #
    cmpt2
    #
    cmpt2
    #
    @10
    cmarrep
    cvv
    @17
    cN
    wceq
    #
    @18
    cR
    wceq
    #
    wa
    #
    vm
    vs
    @20
    @21
    @26
    cB
    @1
    @9
    @30
    @20
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    cB
    @30
    @19
    @31
    cbs
    @17
    cN
    @18
    cR
    cmat
    oveq12
    fveq2d
    cB
    @16
    @32
    marrepfval.b
    cA
    @31
    cbs
    marrepfval.a
    fveq2i
    eqtri
    #
    syl6eqr
    @29
    @21
    @1
    wceq
    @28
    @18
    cR
    cbs
    fveq2
    adantl
    @30
    vk
    vl
    @17
    @17
    @25
    cN
    cN
    @8
    @28
    @29
    simpl
    #
    @34
    @30
    vi
    vj
    @17
    @17
    @24
    cN
    cN
    @7
    @34
    @34
    @29
    @24
    @7
    wceq
    @28
    @29
    @2
    @23
    @5
    @6
    @29
    @3
    @22
    c.0
    @4
    @29
    @22
    cR
    c0g
    cfv
    c.0
    @18
    cR
    c0g
    fveq2
    marrepfval.z
    syl6eqr
    ifeq2d
    ifeq1d
    adantl
    mpt2eq123dv
    mpt2eq123dv
    mpt2eq123dv
    vi
    vj
    vk
    vm
    vn
    vs
    vr
    vl
    df-marrep
    #
    ovmpt2ga
    mpd3an3
    @13
    wn
    #
    @0
    vm
    vs
    c0
    @1
    @9
    cmpt2
    #
    @10
    @36
    @0
    c0
    @37
    vn
    vr
    @27
    cmarrep
    cN
    cR
    cvv
    cvv
    @35
    mpt2ndm0
    vm
    vs
    @1
    @9
    mpt20
    syl6eqr
    @36
    cB
    c0
    wceq
    @1
    @1
    wceq
    @10
    @37
    wceq
    @36
    cB
    @32
    c0
    @33
    cR
    cN
    matbas0pc
    syl5eq
    @36
    @1
    eqidd
    vm
    vs
    cB
    @1
    c0
    @1
    @9
    mpt2eq12
    syl2anc
    eqtr4d
    pm2.61i
    eqtri
end
