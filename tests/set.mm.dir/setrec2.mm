include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "cab.mm"
include "cres.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfeu.mm"
include "nfab.mm"
include "nfres.mm"
include "csetrecs.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wal.mm"
include "cuni.mm"
include "setrec2lem1.mm"
include "sseq1i.mm"
include "imbi2i.mm"
include "albii.mm"
include "imbi1i.mm"
include "abbii.mm"
include "unieqi.mm"
include "df-setrecs.mm"
include "3eqtr4ri.mm"
include "eqtri.mm"
include "setrec2lem2.mm"
include "sylibr.mm"
include "setrec2fun.mm"

theorem setrec2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vk: setvar k
  assume setrec2.1: |- F/_ a F
  assume setrec2.2: |- B = setrecs ( F )
  assume setrec2.3: |- ( ph -> A. a ( a C_ C -> ( F ` a ) C_ C ) )

  disjoint C a
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint ph x
  disjoint ph w
  disjoint k x
  assert |- ( ph -> B C_ C )

  proof
    wph
    cB
    cC
    cF
    vx
    cv
    #
    vu
    cv
    #
    cF
    wbr
    #
    vu
    weu
    #
    vx
    cab
    #
    cres
    #
    va
    va
    cF
    @4
    setrec2.1
    @3
    va
    vx
    @2
    va
    vu
    va
    @0
    @1
    cF
    va
    @0
    nfcv
    setrec2.1
    va
    @1
    nfcv
    nfbr
    nfeu
    nfab
    nfres
    cB
    cF
    csetrecs
    #
    @5
    csetrecs
    #
    setrec2.2
    vw
    cv
    #
    vy
    cv
    #
    wss
    #
    @8
    vz
    cv
    #
    wss
    #
    @8
    @5
    cfv
    #
    @11
    wss
    #
    wi
    #
    wi
    #
    vw
    wal
    #
    @9
    @11
    wss
    #
    wi
    #
    vz
    wal
    #
    vy
    cab
    #
    cuni
    @10
    @12
    @8
    cF
    cfv
    #
    @11
    wss
    #
    wi
    #
    wi
    #
    vw
    wal
    #
    @18
    wi
    #
    vz
    wal
    #
    vy
    cab
    #
    cuni
    @7
    @6
    @21
    @29
    @20
    @28
    vy
    @19
    @27
    vz
    @17
    @26
    @18
    @16
    @25
    vw
    @15
    @24
    @10
    @14
    @23
    @12
    @13
    @22
    @11
    vx
    vu
    cF
    vw
    setrec2lem1
    sseq1i
    imbi2i
    imbi2i
    albii
    imbi1i
    albii
    abbii
    unieqi
    vy
    vz
    vw
    @5
    df-setrecs
    vy
    vz
    vw
    cF
    df-setrecs
    3eqtr4ri
    eqtri
    vx
    vu
    cF
    setrec2lem2
    wph
    va
    cv
    #
    cC
    wss
    #
    @30
    cF
    cfv
    #
    cC
    wss
    #
    wi
    #
    va
    wal
    @31
    @30
    @5
    cfv
    #
    cC
    wss
    #
    wi
    #
    va
    wal
    setrec2.3
    @37
    @34
    va
    @36
    @33
    @31
    @35
    @32
    cC
    vx
    vu
    cF
    va
    setrec2lem1
    sseq1i
    imbi2i
    albii
    sylibr
    setrec2fun
end
