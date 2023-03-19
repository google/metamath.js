include "cn.mm"
include "cz.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "cc0.mm"
include "c1.mm"
include "cneg.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "cif.mm"
include "cmu.mm"
include "df-mu.mm"
include "wcel.mm"
include "0z.mm"
include "cn0.mm"
include "neg1z.mm"
include "cfn.mm"
include "prmdvdsfi.mm"
include "hashcl.mm"
include "syl.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "ifcl.mm"
include "fmpti.mm"

theorem muf
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


  assert |- mmu : NN --> ZZ

  proof
    vx
    cn
    cz
    vp
    cv
    #
    c2
    cexp
    co
    vx
    cv
    #
    cdvds
    wbr
    vp
    cprime
    wrex
    #
    cc0
    c1
    cneg
    #
    @0
    @1
    cdvds
    wbr
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    cexp
    co
    #
    cif
    #
    cmu
    vx
    vp
    df-mu
    @1
    cn
    wcel
    #
    cc0
    cz
    wcel
    @6
    cz
    wcel
    #
    @7
    cz
    wcel
    0z
    @8
    @3
    cz
    wcel
    @5
    cn0
    wcel
    #
    @9
    neg1z
    @8
    @4
    cfn
    wcel
    @10
    @1
    vp
    prmdvdsfi
    @4
    hashcl
    syl
    @3
    @5
    zexpcl
    sylancr
    @2
    cc0
    @6
    cz
    ifcl
    sylancr
    fmpti
end
