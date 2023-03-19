include "cr.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "csu.mm"
include "cchp.mm"
include "df-chp.mm"
include "wcel.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "fsumrecl.mm"
include "fmpti.mm"

theorem chpf
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- psi : RR --> RR

  proof
    vx
    cr
    cr
    c1
    vx
    cv
    #
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
    cchp
    vx
    vn
    df-chp
    @0
    cr
    wcel
    #
    @2
    @4
    vn
    @5
    c1
    @1
    fzfid
    @5
    @3
    @2
    wcel
    #
    wa
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    @6
    @7
    @5
    @3
    @1
    elfznn
    adantl
    @3
    vmacl
    syl
    fsumrecl
    fmpti
end
