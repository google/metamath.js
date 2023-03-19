include "cn.mm"
include "cr.mm"
include "wf.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cdiv.mm"
include "csu.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "wcel.mm"
include "fzfid.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrecred.mm"
include "fsumrecl.mm"
include "nnrp.mm"
include "relogcld.mm"
include "resubcld.mm"
include "fmpti.mm"
include "caddc.mm"
include "peano2nn.mm"
include "nnrpd.mm"
include "pm3.2i.mm"

theorem emcllem1
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  let cH: class H
  let cN: class N
  let cT: class T
  assume emcl.1: |- F = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` n ) ) )
  assume emcl.2: |- G = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` ( n + 1 ) ) ) )

  disjoint m n
  disjoint i k
  disjoint i x
  disjoint F i
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G i
  disjoint G k
  disjoint G x
  disjoint k m
  disjoint H k
  disjoint H m
  disjoint N m
  disjoint N n
  disjoint k n
  disjoint T k
  disjoint m x
  disjoint T m
  disjoint n x
  disjoint T n
  disjoint T x
  assert |- ( F : NN --> RR /\ G : NN --> RR )

  proof
    cn
    cr
    cF
    wf
    cn
    cr
    cG
    wf
    vn
    cn
    cr
    c1
    vn
    cv
    #
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    @0
    clog
    cfv
    #
    cmin
    co
    cF
    emcl.1
    @0
    cn
    wcel
    #
    @4
    @5
    @6
    @1
    @3
    vm
    @6
    c1
    @0
    fzfid
    @6
    @2
    @1
    wcel
    #
    wa
    @2
    @7
    @2
    cn
    wcel
    @6
    @2
    @0
    elfznn
    adantl
    nnrecred
    fsumrecl
    #
    @6
    @0
    @0
    nnrp
    relogcld
    resubcld
    fmpti
    vn
    cn
    cr
    @4
    @0
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    cG
    emcl.2
    @6
    @4
    @10
    @8
    @6
    @9
    @6
    @9
    @0
    peano2nn
    nnrpd
    relogcld
    resubcld
    fmpti
    pm3.2i
end
