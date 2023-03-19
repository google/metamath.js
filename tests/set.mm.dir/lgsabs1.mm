include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cgcd.mm"
include "cr.mm"
include "wb.mm"
include "lgscl.mm"
include "zcnd.mm"
include "abscld.mm"
include "1re.mm"
include "letri3.mm"
include "sylancl.mm"
include "lgsle1.mm"
include "biantrurd.mm"
include "cn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "cn0.mm"
include "wo.mm"
include "nn0abscl.mm"
include "syl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "necon1ad.mm"
include "impbid2.mm"
include "elnnnn0c.mm"
include "baib.mm"
include "cc.mm"
include "abs00.mm"
include "necon3bid.mm"
include "lgsne0.mm"
include "bitrd.mm"
include "3bitr3d.mm"
include "3bitr2d.mm"

theorem lgsabs1
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p


  assert |- ( ( A e. ZZ /\ N e. ZZ ) -> ( ( abs ` ( A /L N ) ) = 1 <-> ( A gcd N ) = 1 ) )

  proof
    cA
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cA
    cN
    clgs
    co
    #
    cabs
    cfv
    #
    c1
    wceq
    #
    @2
    c1
    cle
    wbr
    #
    c1
    @2
    cle
    wbr
    #
    wa
    #
    @5
    cA
    cN
    cgcd
    co
    c1
    wceq
    #
    @0
    @2
    cr
    wcel
    c1
    cr
    wcel
    @3
    @6
    wb
    @0
    @1
    @0
    @1
    cA
    cN
    lgscl
    #
    zcnd
    #
    abscld
    1re
    @2
    c1
    letri3
    sylancl
    @0
    @4
    @5
    cA
    cN
    lgsle1
    biantrurd
    @0
    @2
    cn
    wcel
    #
    @2
    cc0
    wne
    #
    @5
    @7
    @0
    @10
    @11
    @2
    nnne0
    @0
    @10
    @2
    cc0
    @0
    @10
    @2
    cc0
    wceq
    #
    @0
    @2
    cn0
    wcel
    #
    @10
    @12
    wo
    @0
    @1
    cz
    wcel
    @13
    @8
    @1
    nn0abscl
    syl
    #
    @2
    elnn0
    sylib
    ord
    necon1ad
    impbid2
    @0
    @13
    @10
    @5
    wb
    @14
    @10
    @13
    @5
    @2
    elnnnn0c
    baib
    syl
    @0
    @11
    @1
    cc0
    wne
    #
    @7
    @0
    @1
    cc
    wcel
    #
    @11
    @15
    wb
    @9
    @16
    @2
    cc0
    @1
    cc0
    @1
    abs00
    necon3bid
    syl
    cA
    cN
    lgsne0
    bitrd
    3bitr3d
    3bitr2d
end
