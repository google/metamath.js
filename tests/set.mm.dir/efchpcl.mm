include "cr.mm"
include "wcel.mm"
include "cchp.mm"
include "cfv.mm"
include "ce.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "csu.mm"
include "cn.mm"
include "chpval.mm"
include "fveq2d.mm"
include "fzfid.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "efvmacl.mm"
include "efnnfsumcl.mm"
include "eqeltrd.mm"

theorem efchpcl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( A e. RR -> ( exp ` ( psi ` A ) ) e. NN )

  proof
    cA
    cr
    wcel
    #
    cA
    cchp
    cfv
    #
    ce
    cfv
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    vn
    csu
    #
    ce
    cfv
    cn
    @0
    @1
    @6
    ce
    cA
    vn
    chpval
    fveq2d
    @0
    @3
    @5
    vn
    @0
    c1
    @2
    fzfid
    @0
    @4
    @3
    wcel
    #
    wa
    #
    @4
    cn
    wcel
    #
    @5
    cr
    wcel
    @7
    @9
    @0
    @4
    @2
    elfznn
    adantl
    #
    @4
    vmacl
    syl
    @8
    @9
    @5
    ce
    cfv
    cn
    wcel
    @10
    @4
    efvmacl
    syl
    efnnfsumcl
    eqeltrd
end
