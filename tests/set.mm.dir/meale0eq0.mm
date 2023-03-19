include "cfv.mm"
include "cc0.mm"
include "cdm.mm"
include "eqid.mm"
include "meaxrcl.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "a1i.mm"
include "meage0.mm"
include "xrletrid.mm"

theorem meale0eq0
  let wph: wff ph
  let cA: class A
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meale0eq0.m: |- ( ph -> M e. Meas )
  assume meale0eq0.a: |- ( ph -> A e. dom M )
  assume meale0eq0.l: |- ( ph -> ( M ` A ) <_ 0 )


  assert |- ( ph -> ( M ` A ) = 0 )

  proof
    wph
    cA
    cM
    cfv
    cc0
    wph
    cA
    cM
    cdm
    #
    cM
    meale0eq0.m
    @0
    eqid
    meale0eq0.a
    meaxrcl
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    meale0eq0.l
    wph
    cA
    cM
    meale0eq0.m
    meale0eq0.a
    meage0
    xrletrid
end
