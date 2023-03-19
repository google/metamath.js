include "cv.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "cdiv.mm"
include "cfl.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "0zd.mm"
include "hashdvds.mm"
include "wceq.mm"
include "cab.mm"
include "wcel.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "subid1d.mm"
include "breq2d.mm"
include "rabbiia.mm"
include "dfrab3.mm"
include "wrel.mm"
include "reldvds.mm"
include "relimasn.mm"
include "ax-mp.mm"
include "ineq2i.mm"
include "incom.mm"
include "eqtr3i.mm"
include "3eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "cuz.mm"
include "cz.mm"
include "eluzelz.mm"
include "syl.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "peano2zm.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem hashnzfz
  let wph: wff ph
  let cJ: class J
  let cK: class K
  let cN: class N
  let vx: setvar x
  assume hashnzfz.n: |- ( ph -> N e. NN )
  assume hashnzfz.j: |- ( ph -> J e. ZZ )
  assume hashnzfz.k: |- ( ph -> K e. ( ZZ>= ` ( J - 1 ) ) )


  assert |- ( ph -> ( # ` ( ( || " { N } ) i^i ( J ... K ) ) ) = ( ( |_ ` ( K / N ) ) - ( |_ ` ( ( J - 1 ) / N ) ) ) )

  proof
    wph
    cN
    vx
    cv
    #
    cc0
    cmin
    co
    #
    cdvds
    wbr
    #
    vx
    cJ
    cK
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    cK
    cc0
    cmin
    co
    #
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cJ
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    #
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    cdvds
    cN
    csn
    cima
    #
    @3
    cin
    #
    chash
    cfv
    #
    cK
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    @9
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    wph
    vx
    cJ
    cK
    cc0
    cN
    hashnzfz.n
    hashnzfz.j
    hashnzfz.k
    wph
    0zd
    hashdvds
    @5
    @15
    wceq
    wph
    @4
    @14
    chash
    @4
    cN
    @0
    cdvds
    wbr
    #
    vx
    @3
    crab
    @3
    @20
    vx
    cab
    #
    cin
    #
    @14
    @2
    @20
    vx
    @3
    @0
    @3
    wcel
    #
    @1
    @0
    cN
    cdvds
    @23
    @0
    @23
    @0
    @0
    cJ
    cK
    elfzelz
    zcnd
    subid1d
    breq2d
    rabbiia
    @20
    vx
    @3
    dfrab3
    @3
    @13
    cin
    @22
    @14
    @13
    @21
    @3
    cdvds
    wrel
    @13
    @21
    wceq
    reldvds
    vx
    cN
    cdvds
    relimasn
    ax-mp
    ineq2i
    @3
    @13
    incom
    eqtr3i
    3eqtri
    fveq2i
    a1i
    wph
    @8
    @17
    @12
    @19
    cmin
    wph
    @7
    @16
    cfl
    wph
    @6
    cK
    cN
    cdiv
    wph
    cK
    wph
    cK
    wph
    cK
    @9
    cuz
    cfv
    wcel
    cK
    cz
    wcel
    hashnzfz.k
    @9
    cK
    eluzelz
    syl
    zcnd
    subid1d
    oveq1d
    fveq2d
    wph
    @11
    @18
    cfl
    wph
    @10
    @9
    cN
    cdiv
    wph
    @9
    wph
    @9
    wph
    cJ
    cz
    wcel
    @9
    cz
    wcel
    hashnzfz.j
    cJ
    peano2zm
    syl
    zcnd
    subid1d
    oveq1d
    fveq2d
    oveq12d
    3eqtr3d
end
