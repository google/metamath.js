include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "cdiv.mm"
include "csu.mm"
include "clog.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cioo.mm"
include "cmul.mm"
include "c2.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "vmadivsumb.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "2vmadivsumlem.mm"
include "rexlimiva.mm"
include "ax-mp.mm"

theorem 2vmadivsum
  let vx: setvar x
  let vm: setvar m
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vy: setvar y
  let cN: class N

  disjoint m n
  disjoint m x
  disjoint n x
  disjoint c d
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint N c
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d x
  disjoint d y
  disjoint N d
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i x
  disjoint i y
  disjoint N i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint N j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint m u
  disjoint m y
  disjoint N m
  disjoint n u
  disjoint n y
  disjoint N n
  disjoint u x
  disjoint u y
  disjoint N u
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( Lam ` n ) / n ) x. sum_ m e. ( 1 ... ( |_ ` ( x / n ) ) ) ( ( Lam ` m ) / m ) ) / ( log ` x ) ) - ( ( log ` x ) / 2 ) ) ) e. O(1)

  proof
    c1
    vy
    cv
    #
    cfl
    cfv
    cfz
    co
    vi
    cv
    #
    cvma
    cfv
    @1
    cdiv
    co
    vi
    csu
    @0
    clog
    cfv
    cmin
    co
    cabs
    cfv
    vc
    cv
    #
    cle
    wbr
    vy
    c1
    cpnf
    cico
    co
    wral
    #
    vc
    crp
    wrex
    vx
    c1
    cpnf
    cioo
    co
    c1
    vx
    cv
    #
    cfl
    cfv
    cfz
    co
    vn
    cv
    #
    cvma
    cfv
    @5
    cdiv
    co
    c1
    @4
    @5
    cdiv
    co
    cfl
    cfv
    cfz
    co
    vm
    cv
    #
    cvma
    cfv
    @6
    cdiv
    co
    vm
    csu
    cmul
    co
    vn
    csu
    @4
    clog
    cfv
    #
    cdiv
    co
    @7
    c2
    cdiv
    co
    cmin
    co
    cmpt
    co1
    wcel
    #
    vy
    vi
    vc
    vmadivsumb
    @3
    @8
    vc
    crp
    @2
    crp
    wcel
    #
    @3
    wa
    vx
    vy
    @2
    vi
    vm
    vn
    @9
    @3
    simpl
    @9
    @3
    simpr
    2vmadivsumlem
    rexlimiva
    ax-mp
end
