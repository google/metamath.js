include "wcel.mm"
include "wa.mm"
include "cspthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "ctrlson.mm"
include "cspths.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "w3a.mm"
include "isspthson.mm"
include "wb.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "istrlson.mm"
include "adantr.mm"
include "cpths.mm"
include "spthispth.mm"
include "pthistrl.mm"
include "syl.mm"
include "adantl.mm"
include "biantrud.mm"
include "cwlks.mm"
include "trliswlk.mm"
include "iswlkon.mm"
include "3anass.mm"
include "syl6bb.mm"
include "mpbirand.mm"
include "3bitr2d.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "ancom.mm"
include "bitr2i.mm"
include "bitrd.mm"

theorem isspthonpth
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume isspthonpth.v: |- V = ( Vtx ` G )


  assert |- ( ( ( A e. V /\ B e. V ) /\ ( F e. W /\ P e. Z ) ) -> ( F ( A ( SPathsOn ` G ) B ) P <-> ( F ( SPaths ` G ) P /\ ( P ` 0 ) = A /\ ( P ` ( # ` F ) ) = B ) ) )

  proof
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    cF
    cW
    wcel
    cP
    cZ
    wcel
    wa
    wa
    #
    cF
    cP
    cA
    cB
    cG
    cspthson
    cfv
    co
    wbr
    cF
    cP
    cA
    cB
    cG
    ctrlson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    wa
    #
    @2
    cc0
    cP
    cfv
    cA
    wceq
    #
    cF
    chash
    cfv
    cP
    cfv
    cB
    wceq
    #
    w3a
    #
    cA
    cB
    cP
    cW
    cF
    cG
    cV
    cZ
    isspthonpth.v
    isspthson
    @0
    @3
    @4
    @5
    wa
    #
    @2
    wa
    #
    @6
    @0
    @2
    @1
    @7
    @0
    @2
    @1
    @7
    wb
    @0
    @2
    wa
    #
    @1
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    wa
    #
    @10
    @7
    @0
    @1
    @12
    wb
    @2
    cA
    cB
    cP
    cW
    cF
    cG
    cV
    cZ
    isspthonpth.v
    istrlson
    adantr
    @9
    @11
    @10
    @2
    @11
    @0
    @2
    cF
    cP
    cG
    cpths
    cfv
    wbr
    @11
    cP
    cF
    cG
    spthispth
    cP
    cF
    cG
    pthistrl
    syl
    #
    adantl
    biantrud
    @9
    @10
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @7
    @2
    @14
    @0
    @2
    @11
    @14
    @13
    cP
    cF
    cG
    trliswlk
    syl
    adantl
    @0
    @10
    @14
    @7
    wa
    #
    wb
    @2
    @0
    @10
    @14
    @4
    @5
    w3a
    @15
    cA
    cB
    cP
    cW
    cF
    cG
    cV
    cZ
    isspthonpth.v
    iswlkon
    @14
    @4
    @5
    3anass
    syl6bb
    adantr
    mpbirand
    3bitr2d
    ex
    pm5.32rd
    @6
    @2
    @7
    wa
    @8
    @2
    @4
    @5
    3anass
    @2
    @7
    ancom
    bitr2i
    syl6bb
    bitrd
end
