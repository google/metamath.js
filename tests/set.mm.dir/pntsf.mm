include "cr.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "clog.mm"
include "cdiv.mm"
include "cchp.mm"
include "caddc.mm"
include "cmul.mm"
include "csu.mm"
include "wcel.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "simpl.mm"
include "nndivred.mm"
include "chpcl.mm"
include "readdcld.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "fmpti.mm"

theorem pntsf
  let cS: class S
  let vi: setvar i
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let wph: wff ph
  let cR: class R
  let cT: class T
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )

  disjoint a i
  disjoint a c
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
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
  disjoint S c
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint T m
  disjoint T n
  assert |- S : RR --> RR

  proof
    va
    cr
    cr
    c1
    va
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vi
    cv
    #
    cvma
    cfv
    #
    @3
    clog
    cfv
    #
    @0
    @3
    cdiv
    co
    #
    cchp
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    vi
    csu
    cS
    pntsval.1
    @0
    cr
    wcel
    #
    @2
    @9
    vi
    @10
    c1
    @1
    fzfid
    @10
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @8
    @12
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    @11
    @13
    @10
    @3
    @1
    elfznn
    adantl
    #
    @3
    vmacl
    syl
    @12
    @5
    @7
    @12
    @3
    @12
    @3
    @14
    nnrpd
    relogcld
    @12
    @6
    cr
    wcel
    @7
    cr
    wcel
    @12
    @0
    @3
    @10
    @11
    simpl
    @14
    nndivred
    @6
    chpcl
    syl
    readdcld
    remulcld
    fsumrecl
    fmpti
end
