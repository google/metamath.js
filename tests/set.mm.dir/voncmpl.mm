include "covoln.mm"
include "cfv.mm"
include "ccaragen.mm"
include "cdm.mm"
include "cuni.mm"
include "ovnome.mm"
include "eqid.mm"
include "wcel.mm"
include "wss.mm"
include "cvoln.mm"
include "dmvon.mm"
include "come.mm"
include "caragenss.mm"
include "syl.mm"
include "eqsstrd.mm"
include "sseldd.mm"
include "elssuni.mm"
include "sstrd.mm"
include "cc0.mm"
include "cres.mm"
include "eqcomd.mm"
include "vonval.mm"
include "fveq1d.mm"
include "eqtrd.mm"
include "wceq.mm"
include "a1i.mm"
include "eqtr2d.mm"
include "reseq2d.mm"
include "syl6eleqr.mm"
include "fvres.mm"
include "3eqtrrd.mm"
include "omess0.mm"
include "caragencmpl.mm"
include "eleqtrd.mm"

theorem voncmpl
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cF: class F
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume voncmpl.x: |- ( ph -> X e. Fin )
  assume voncmpl.s: |- S = dom ( voln ` X )
  assume voncmpl.e: |- ( ph -> E e. dom ( voln ` X ) )
  assume voncmpl.z: |- ( ph -> ( ( voln ` X ) ` E ) = 0 )
  assume voncmpl.f: |- ( ph -> F C_ E )


  assert |- ( ph -> F e. S )

  proof
    wph
    cF
    cX
    covoln
    cfv
    #
    ccaragen
    cfv
    #
    cS
    wph
    @1
    cF
    @0
    @0
    cdm
    #
    cuni
    #
    wph
    cX
    voncmpl.x
    ovnome
    #
    @3
    eqid
    #
    wph
    cF
    cE
    @3
    voncmpl.f
    wph
    cE
    @2
    wcel
    cE
    @3
    wss
    wph
    cX
    cvoln
    cfv
    #
    cdm
    #
    @2
    cE
    wph
    @7
    @1
    @2
    wph
    cX
    voncmpl.x
    dmvon
    #
    wph
    @0
    come
    wcel
    @1
    @2
    wss
    @4
    @1
    @0
    @1
    eqid
    #
    caragenss
    syl
    eqsstrd
    voncmpl.e
    sseldd
    cE
    @2
    elssuni
    syl
    #
    sstrd
    wph
    cE
    cF
    @0
    @3
    @4
    @5
    @10
    wph
    cc0
    cE
    @0
    @1
    cres
    #
    cfv
    #
    cE
    @0
    cS
    cres
    #
    cfv
    #
    cE
    @0
    cfv
    #
    wph
    cc0
    cE
    @6
    cfv
    #
    @12
    wph
    @16
    cc0
    voncmpl.z
    eqcomd
    wph
    cE
    @6
    @11
    wph
    cX
    voncmpl.x
    vonval
    fveq1d
    eqtrd
    wph
    cE
    @11
    @13
    wph
    @1
    cS
    @0
    wph
    cS
    @7
    @1
    cS
    @7
    wceq
    wph
    voncmpl.s
    a1i
    @8
    eqtr2d
    #
    reseq2d
    fveq1d
    wph
    cE
    cS
    wcel
    @14
    @15
    wceq
    wph
    cE
    @7
    cS
    voncmpl.e
    voncmpl.s
    syl6eleqr
    cE
    cS
    @0
    fvres
    syl
    3eqtrrd
    voncmpl.f
    omess0
    @9
    caragencmpl
    @17
    eleqtrd
end
