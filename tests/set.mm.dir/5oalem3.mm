include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cmv.mm"
include "cph.mm"
include "cin.mm"
include "anandir.mm"
include "5oalem2.mm"
include "anim12i.mm"
include "an4s.mm"
include "sylanb.mm"
include "shscli.mm"
include "shincli.mm"
include "shsvsi.mm"
include "syl.mm"
include "wb.mm"
include "chil.mm"
include "sheli.mm"
include "adantr.mm"
include "hvsubsub4.mm"
include "anandirs.mm"
include "c0v.mm"
include "hvsubid.mm"
include "oveq2d.mm"
include "hvsubcl.mm"
include "hvsub0.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "syl2an.mm"
include "eleq1d.mm"
include "mpbid.mm"

theorem 5oalem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  assume 5oalem3.1: |- A e. SH
  assume 5oalem3.2: |- B e. SH
  assume 5oalem3.3: |- C e. SH
  assume 5oalem3.4: |- D e. SH
  assume 5oalem3.5: |- F e. SH
  assume 5oalem3.6: |- G e. SH


  assert |- ( ( ( ( ( x e. A /\ y e. B ) /\ ( z e. C /\ w e. D ) ) /\ ( f e. F /\ g e. G ) ) /\ ( ( x +h y ) = ( f +h g ) /\ ( z +h w ) = ( f +h g ) ) ) -> ( x -h z ) e. ( ( ( A +H F ) i^i ( B +H G ) ) +H ( ( C +H F ) i^i ( D +H G ) ) ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vz
    cv
    #
    cC
    wcel
    #
    vw
    cv
    #
    cD
    wcel
    #
    wa
    #
    wa
    #
    vf
    cv
    #
    cF
    wcel
    #
    vg
    cv
    #
    cG
    wcel
    #
    wa
    #
    wa
    #
    @0
    @2
    cva
    co
    @11
    @13
    cva
    co
    #
    wceq
    #
    @5
    @7
    cva
    co
    @17
    wceq
    #
    wa
    #
    wa
    #
    @0
    @11
    cmv
    co
    #
    @5
    @11
    cmv
    co
    #
    cmv
    co
    #
    cA
    cF
    cph
    co
    #
    cB
    cG
    cph
    co
    #
    cin
    #
    cC
    cF
    cph
    co
    #
    cD
    cG
    cph
    co
    #
    cin
    #
    cph
    co
    #
    wcel
    #
    @0
    @5
    cmv
    co
    #
    @31
    wcel
    #
    @21
    @22
    @27
    wcel
    #
    @23
    @30
    wcel
    #
    wa
    #
    @32
    @16
    @4
    @15
    wa
    #
    @9
    @15
    wa
    #
    wa
    @20
    @37
    @4
    @9
    @15
    anandir
    @38
    @18
    @39
    @19
    @37
    @38
    @18
    wa
    @35
    @39
    @19
    wa
    @36
    vx
    vy
    vf
    vg
    cA
    cB
    cF
    cG
    5oalem3.1
    5oalem3.2
    5oalem3.5
    5oalem3.6
    5oalem2
    vz
    vw
    vf
    vg
    cC
    cD
    cF
    cG
    5oalem3.3
    5oalem3.4
    5oalem3.5
    5oalem3.6
    5oalem2
    anim12i
    an4s
    sylanb
    @27
    @30
    @22
    @23
    @25
    @26
    cA
    cF
    5oalem3.1
    5oalem3.5
    shscli
    cB
    cG
    5oalem3.2
    5oalem3.6
    shscli
    shincli
    @28
    @29
    cC
    cF
    5oalem3.3
    5oalem3.5
    shscli
    cD
    cG
    5oalem3.4
    5oalem3.6
    shscli
    shincli
    shsvsi
    syl
    @16
    @32
    @34
    wb
    @20
    @16
    @24
    @33
    @31
    @10
    @0
    chil
    wcel
    #
    @5
    chil
    wcel
    #
    wa
    #
    @11
    chil
    wcel
    #
    @24
    @33
    wceq
    @15
    @4
    @40
    @9
    @41
    @1
    @40
    @3
    @0
    cA
    5oalem3.1
    sheli
    adantr
    @6
    @41
    @8
    @5
    cC
    5oalem3.3
    sheli
    adantr
    anim12i
    @12
    @43
    @14
    @11
    cF
    5oalem3.5
    sheli
    adantr
    @42
    @43
    wa
    @24
    @33
    @11
    @11
    cmv
    co
    #
    cmv
    co
    #
    @33
    @40
    @41
    @43
    @24
    @45
    wceq
    @0
    @11
    @5
    @11
    hvsubsub4
    anandirs
    @43
    @42
    @45
    @33
    c0v
    cmv
    co
    #
    @33
    @43
    @44
    c0v
    @33
    cmv
    @11
    hvsubid
    oveq2d
    @42
    @33
    chil
    wcel
    @46
    @33
    wceq
    @0
    @5
    hvsubcl
    @33
    hvsub0
    syl
    sylan9eqr
    eqtrd
    syl2an
    eleq1d
    adantr
    mpbid
end
