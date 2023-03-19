include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "cmu.mm"
include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "cle.mm"
include "wa.mm"
include "cc0.mm"
include "cneg.mm"
include "crab.mm"
include "chash.mm"
include "cif.mm"
include "muval.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "fveq2d.mm"
include "abs0.mm"
include "0le1.mm"
include "eqbrtri.mm"
include "syl6eqbr.mm"
include "wn.mm"
include "iffalse.mm"
include "wceq.mm"
include "cc.mm"
include "cn0.mm"
include "neg1cn.mm"
include "cfn.mm"
include "prmdvdsfi.mm"
include "hashcl.mm"
include "syl.mm"
include "absexp.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "cz.mm"
include "nn0zd.mm"
include "1exp.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "adantr.mm"
include "1le1.mm"
include "pm2.61dan.mm"

theorem mule1
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


  assert |- ( A e. NN -> ( abs ` ( mmu ` A ) ) <_ 1 )

  proof
    cA
    cn
    wcel
    #
    vp
    cv
    #
    c2
    cexp
    co
    cA
    cdvds
    wbr
    vp
    cprime
    wrex
    #
    cA
    cmu
    cfv
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    @0
    @2
    wa
    #
    @4
    cc0
    cabs
    cfv
    #
    c1
    cle
    @5
    @3
    cc0
    cabs
    @0
    @2
    @3
    @2
    cc0
    c1
    cneg
    #
    @1
    cA
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
    cc0
    cA
    vp
    muval
    #
    @2
    cc0
    @10
    iftrue
    sylan9eq
    fveq2d
    @6
    cc0
    c1
    cle
    abs0
    0le1
    eqbrtri
    syl6eqbr
    @0
    @2
    wn
    #
    wa
    #
    @4
    c1
    c1
    cle
    @14
    @4
    @10
    cabs
    cfv
    #
    c1
    @14
    @3
    @10
    cabs
    @0
    @13
    @3
    @11
    @10
    @12
    @2
    cc0
    @10
    iffalse
    sylan9eq
    fveq2d
    @0
    @15
    c1
    wceq
    @13
    @0
    @15
    @7
    cabs
    cfv
    #
    @9
    cexp
    co
    #
    c1
    @0
    @7
    cc
    wcel
    @9
    cn0
    wcel
    #
    @15
    @17
    wceq
    neg1cn
    @0
    @8
    cfn
    wcel
    @18
    cA
    vp
    prmdvdsfi
    @8
    hashcl
    syl
    #
    @7
    @9
    absexp
    sylancr
    @0
    @17
    c1
    @9
    cexp
    co
    #
    c1
    @16
    c1
    @9
    cexp
    @16
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    oveq1i
    @0
    @9
    cz
    wcel
    @20
    c1
    wceq
    @0
    @9
    @19
    nn0zd
    @9
    1exp
    syl
    syl5eq
    eqtrd
    adantr
    eqtrd
    1le1
    syl6eqbr
    pm2.61dan
end
