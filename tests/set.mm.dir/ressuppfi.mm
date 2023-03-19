include "cres.mm"
include "csupp.mm"
include "co.mm"
include "cdm.mm"
include "cdif.mm"
include "cun.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqeltrd.mm"
include "unfi.mm"
include "syl2anc.mm"
include "ressuppssdif.mm"
include "ssfi.mm"

theorem ressuppfi
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume ressuppfi.b: |- ( ph -> ( dom F \ B ) e. Fin )
  assume ressuppfi.f: |- ( ph -> F e. W )
  assume ressuppfi.g: |- ( ph -> G = ( F |` B ) )
  assume ressuppfi.s: |- ( ph -> ( G supp Z ) e. Fin )
  assume ressuppfi.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( F supp Z ) e. Fin )

  proof
    wph
    cF
    cB
    cres
    #
    cZ
    csupp
    co
    #
    cF
    cdm
    cB
    cdif
    #
    cun
    #
    cfn
    wcel
    #
    cF
    cZ
    csupp
    co
    #
    @3
    wss
    #
    @5
    cfn
    wcel
    wph
    @1
    cfn
    wcel
    @2
    cfn
    wcel
    @4
    wph
    @1
    cG
    cZ
    csupp
    co
    cfn
    wph
    @0
    cG
    cZ
    csupp
    wph
    cG
    @0
    ressuppfi.g
    eqcomd
    oveq1d
    ressuppfi.s
    eqeltrd
    ressuppfi.b
    @1
    @2
    unfi
    syl2anc
    wph
    cF
    cW
    wcel
    cZ
    cV
    wcel
    @6
    ressuppfi.f
    ressuppfi.z
    cB
    cF
    cW
    cV
    cZ
    ressuppssdif
    syl2anc
    @3
    @5
    ssfi
    syl2anc
end
