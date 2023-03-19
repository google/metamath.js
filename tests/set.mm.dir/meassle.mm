include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "meaxrcl.mm"
include "csalg.mm"
include "wcel.mm"
include "dmmeasal.mm"
include "saldifcl2.mm"
include "syl3anc.mm"
include "meacl.mm"
include "xadd0ge.mm"
include "cun.mm"
include "wss.mm"
include "wceq.mm"
include "undif.mm"
include "biimpi.mm"
include "syl.mm"
include "fveq2d.mm"
include "eqcomd.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "a1i.mm"
include "meadjun.mm"
include "eqtr2d.mm"
include "breqtrd.mm"

theorem meassle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meassle.m: |- ( ph -> M e. Meas )
  assume meassle.x: |- S = dom M
  assume meassle.a: |- ( ph -> A e. S )
  assume meassle.b: |- ( ph -> B e. S )
  assume meassle.ss: |- ( ph -> A C_ B )


  assert |- ( ph -> ( M ` A ) <_ ( M ` B ) )

  proof
    wph
    cA
    cM
    cfv
    #
    @0
    cB
    cA
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    cB
    cM
    cfv
    #
    cle
    wph
    @0
    @2
    wph
    cA
    cS
    cM
    meassle.m
    meassle.x
    meassle.a
    meaxrcl
    wph
    @1
    cS
    cM
    meassle.m
    meassle.x
    wph
    cS
    csalg
    wcel
    cB
    cS
    wcel
    cA
    cS
    wcel
    @1
    cS
    wcel
    wph
    cS
    cM
    meassle.m
    meassle.x
    dmmeasal
    meassle.b
    meassle.a
    cS
    cB
    cA
    saldifcl2
    syl3anc
    #
    meacl
    xadd0ge
    wph
    @4
    cA
    @1
    cun
    #
    cM
    cfv
    #
    @3
    wph
    @7
    @4
    wph
    @6
    cB
    cM
    wph
    cA
    cB
    wss
    #
    @6
    cB
    wceq
    #
    meassle.ss
    @8
    @9
    cA
    cB
    undif
    biimpi
    syl
    fveq2d
    eqcomd
    wph
    cA
    @1
    cS
    cM
    meassle.m
    meassle.x
    meassle.a
    @5
    cA
    @1
    cin
    c0
    wceq
    wph
    cA
    cB
    disjdif
    a1i
    meadjun
    eqtr2d
    breqtrd
end
