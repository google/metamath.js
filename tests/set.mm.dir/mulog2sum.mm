include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "clog.mm"
include "cdiv.mm"
include "csu.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cmpt.mm"
include "crli.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "wex.mm"
include "cmu.mm"
include "cmul.mm"
include "co1.mm"
include "cr.mm"
include "wf.mm"
include "ceu.mm"
include "cle.mm"
include "w3a.mm"
include "cabs.mm"
include "wi.mm"
include "eqid.mm"
include "logdivsum.mm"
include "simp2i.mm"
include "eldmg.mm"
include "ibi.mm"
include "id.mm"
include "mulog2sumlem3.mm"
include "exlimiv.mm"
include "mp2b.mm"

theorem mulog2sum
  let vx: setvar x
  let vn: setvar n
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z

  disjoint n x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( mmu ` n ) / n ) x. ( ( log ` ( x / n ) ) ^ 2 ) ) - ( 2 x. ( log ` x ) ) ) ) e. O(1)

  proof
    vy
    crp
    c1
    vy
    cv
    #
    cfl
    cfv
    cfz
    co
    vm
    cv
    #
    clog
    cfv
    @1
    cdiv
    co
    vm
    csu
    @0
    clog
    cfv
    c2
    cexp
    co
    c2
    cdiv
    co
    cmin
    co
    cmpt
    #
    crli
    cdm
    #
    wcel
    #
    @2
    vz
    cv
    #
    crli
    wbr
    #
    vz
    wex
    #
    vx
    crp
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
    cmu
    cfv
    @9
    cdiv
    co
    @8
    @9
    cdiv
    co
    clog
    cfv
    c2
    cexp
    co
    cmul
    co
    vn
    csu
    c2
    @8
    clog
    cfv
    cmul
    co
    cmin
    co
    cmpt
    co1
    wcel
    #
    crp
    cr
    @2
    wf
    @4
    @2
    c1
    crli
    wbr
    c1
    crp
    wcel
    ceu
    c1
    cle
    wbr
    w3a
    c1
    @2
    cfv
    c1
    cmin
    co
    cabs
    cfv
    c1
    clog
    cfv
    c1
    cdiv
    co
    cle
    wbr
    wi
    vy
    c1
    vm
    @2
    c1
    @2
    eqid
    #
    logdivsum
    simp2i
    @4
    @7
    vz
    @2
    crli
    @3
    eldmg
    ibi
    @6
    @10
    vz
    @6
    vx
    vy
    vm
    vn
    @2
    @5
    @11
    @6
    id
    mulog2sumlem3
    exlimiv
    mp2b
end
