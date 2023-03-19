include "cc0.mm"
include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cdm.mm"
include "eqid.mm"
include "meacl.mm"
include "iccgelb.mm"
include "syl3anc.mm"

theorem meage0
  let wph: wff ph
  let cA: class A
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meage0.m: |- ( ph -> M e. Meas )
  assume meage0.a: |- ( ph -> A e. dom M )


  assert |- ( ph -> 0 <_ ( M ` A ) )

  proof
    wph
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cA
    cM
    cfv
    #
    cc0
    cpnf
    cicc
    co
    wcel
    cc0
    @2
    cle
    wbr
    @0
    wph
    0xr
    a1i
    @1
    wph
    pnfxr
    a1i
    wph
    cA
    cM
    cdm
    #
    cM
    meage0.m
    @3
    eqid
    meage0.a
    meacl
    cc0
    cpnf
    @2
    iccgelb
    syl3anc
end
