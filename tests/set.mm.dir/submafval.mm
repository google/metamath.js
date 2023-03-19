include "csubma.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cmat.mm"
include "cbs.mm"
include "cfv.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "difeq1.mm"
include "adantr.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "mpteq12dv.mm"
include "df-subma.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "mpt0.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "matbas0pc.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem submafval
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let vl: setvar l
  let vn: setvar n
  let vr: setvar r
  assume submafval.a: |- A = ( N Mat R )
  assume submafval.q: |- Q = ( N subMat R )
  assume submafval.b: |- B = ( Base ` A )

  disjoint B m
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint R m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
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
  assert |- Q = ( m e. B |-> ( k e. N , l e. N |-> ( i e. ( N \ { k } ) , j e. ( N \ { l } ) |-> ( i m j ) ) ) )

  proof
    cQ
    cN
    cR
    csubma
    co
    #
    vm
    cB
    vk
    vl
    cN
    cN
    vi
    vj
    cN
    vk
    cv
    csn
    #
    cdif
    #
    cN
    vl
    cv
    csn
    #
    cdif
    #
    vi
    cv
    vj
    cv
    vm
    cv
    co
    #
    cmpt2
    #
    cmpt2
    #
    cmpt
    #
    submafval.q
    cN
    cvv
    wcel
    cR
    cvv
    wcel
    wa
    #
    @0
    @8
    wceq
    vn
    vr
    cN
    cR
    cvv
    cvv
    vm
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
    vk
    vl
    @10
    @10
    vi
    vj
    @10
    @1
    cdif
    #
    @10
    @3
    cdif
    #
    @5
    cmpt2
    #
    cmpt2
    #
    cmpt
    #
    @8
    csubma
    @10
    cN
    wceq
    #
    @11
    cR
    wceq
    #
    wa
    #
    vm
    @13
    @17
    cB
    @7
    @21
    @13
    cA
    cbs
    cfv
    #
    cB
    @21
    @12
    cA
    cbs
    @21
    @12
    cN
    cR
    cmat
    co
    #
    cA
    @10
    cN
    @11
    cR
    cmat
    oveq12
    submafval.a
    syl6eqr
    fveq2d
    submafval.b
    syl6eqr
    @21
    vk
    vl
    @10
    @10
    @16
    cN
    cN
    @6
    @19
    @20
    simpl
    #
    @24
    @21
    vi
    vj
    @14
    @15
    @5
    @2
    @4
    @5
    @19
    @14
    @2
    wceq
    @20
    @10
    cN
    @1
    difeq1
    adantr
    @19
    @15
    @4
    wceq
    @20
    @10
    cN
    @3
    difeq1
    adantr
    @21
    @5
    eqidd
    mpt2eq123dv
    mpt2eq123dv
    mpteq12dv
    vi
    vj
    vk
    vm
    vn
    vr
    vl
    df-subma
    #
    vm
    cB
    @7
    cB
    @22
    cvv
    submafval.b
    cA
    cbs
    fvex
    eqeltri
    mptex
    ovmpt2a
    @9
    wn
    #
    @0
    vm
    c0
    @7
    cmpt
    #
    @8
    @26
    @0
    c0
    @27
    vn
    vr
    @18
    csubma
    cN
    cR
    cvv
    cvv
    @25
    mpt2ndm0
    vm
    @7
    mpt0
    syl6eqr
    @26
    vm
    cB
    c0
    @7
    @26
    cB
    @23
    cbs
    cfv
    #
    c0
    cB
    @22
    @28
    submafval.b
    cA
    @23
    cbs
    submafval.a
    fveq2i
    eqtri
    cR
    cN
    matbas0pc
    syl5eq
    mpteq1d
    eqtr4d
    pm2.61i
    eqtri
end
