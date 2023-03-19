include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "c2.mm"
include "clog.mm"
include "cmul.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cfl.mm"
include "cfz.mm"
include "cvma.mm"
include "cchp.mm"
include "caddc.mm"
include "csu.mm"
include "selbergb.mm"
include "wcel.mm"
include "cr.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "simplbi.mm"
include "pntsval.mm"
include "syl.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbiia.mm"
include "rexbii.mm"
include "mpbir.mm"

theorem selbergsb
  let vx: setvar x
  let cS: class S
  let vi: setvar i
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let cA: class A
  let cB: class B
  let wph: wff ph
  let cR: class R
  let cT: class T
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )

  disjoint a c
  disjoint a i
  disjoint a x
  disjoint c i
  disjoint c x
  disjoint i x
  disjoint S c
  disjoint S x
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a y
  disjoint A a
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S y
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint T m
  disjoint T n
  assert |- E. c e. RR+ A. x e. ( 1 [,) +oo ) ( abs ` ( ( ( S ` x ) / x ) - ( 2 x. ( log ` x ) ) ) ) <_ c

  proof
    vx
    cv
    #
    cS
    cfv
    #
    @0
    cdiv
    co
    #
    c2
    @0
    clog
    cfv
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vx
    c1
    cpnf
    cico
    co
    #
    wral
    #
    vc
    crp
    wrex
    c1
    @0
    cfl
    cfv
    cfz
    co
    vn
    cv
    #
    cvma
    cfv
    @10
    clog
    cfv
    @0
    @10
    cdiv
    co
    cchp
    cfv
    caddc
    co
    cmul
    co
    vn
    csu
    #
    @0
    cdiv
    co
    #
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    cle
    wbr
    #
    vx
    @8
    wral
    #
    vc
    crp
    wrex
    vx
    vn
    vc
    selbergb
    @9
    @16
    vc
    crp
    @7
    @15
    vx
    @8
    @0
    @8
    wcel
    #
    @5
    @14
    @6
    cle
    @17
    @4
    @13
    cabs
    @17
    @2
    @12
    @3
    cmin
    @17
    @1
    @11
    @0
    cdiv
    @17
    @0
    cr
    wcel
    #
    @1
    @11
    wceq
    @17
    @18
    c1
    @0
    cle
    wbr
    #
    c1
    cr
    wcel
    @17
    @18
    @19
    wa
    wb
    1re
    c1
    @0
    elicopnf
    ax-mp
    simplbi
    @0
    cS
    vi
    vn
    va
    pntsval.1
    pntsval
    syl
    oveq1d
    oveq1d
    fveq2d
    breq1d
    ralbiia
    rexbii
    mpbir
end
