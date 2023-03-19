include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cneg.mm"
include "clgs.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "neg0.mm"
include "simpr.mm"
include "negeqd.mm"
include "3eqtr4a.mm"
include "oveq2d.mm"
include "wne.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cif.mm"
include "cmul.mm"
include "nn0z.mm"
include "lgsneg.mm"
include "syl3an1.mm"
include "wn.mm"
include "nn0nlt0.mm"
include "3ad2ant1.mm"
include "iffalsed.mm"
include "oveq1d.mm"
include "simp2.mm"
include "lgscl.mm"
include "syl2anc.mm"
include "zcnd.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "3expa.mm"
include "pm2.61dane.mm"

theorem lgsneg1
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


  assert |- ( ( A e. NN0 /\ N e. ZZ ) -> ( A /L -u N ) = ( A /L N ) )

  proof
    cA
    cn0
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    cN
    cneg
    #
    clgs
    co
    #
    cA
    cN
    clgs
    co
    #
    wceq
    #
    cN
    cc0
    @2
    cN
    cc0
    wceq
    #
    wa
    #
    @3
    cN
    cA
    clgs
    @8
    cc0
    cneg
    cc0
    @3
    cN
    neg0
    @8
    cN
    cc0
    @2
    @7
    simpr
    #
    negeqd
    @9
    3eqtr4a
    oveq2d
    @0
    @1
    cN
    cc0
    wne
    #
    @6
    @0
    @1
    @10
    w3a
    #
    @4
    cA
    cc0
    clt
    wbr
    #
    c1
    cneg
    #
    c1
    cif
    #
    @5
    cmul
    co
    #
    c1
    @5
    cmul
    co
    @5
    @0
    cA
    cz
    wcel
    #
    @1
    @10
    @4
    @15
    wceq
    cA
    nn0z
    #
    cA
    cN
    lgsneg
    syl3an1
    @11
    @14
    c1
    @5
    cmul
    @11
    @12
    @13
    c1
    @0
    @1
    @12
    wn
    @10
    cA
    nn0nlt0
    3ad2ant1
    iffalsed
    oveq1d
    @11
    @5
    @11
    @5
    @11
    @16
    @1
    @5
    cz
    wcel
    @0
    @1
    @16
    @10
    @17
    3ad2ant1
    @0
    @1
    @10
    simp2
    cA
    cN
    lgscl
    syl2anc
    zcnd
    mulid2d
    3eqtrd
    3expa
    pm2.61dane
end
