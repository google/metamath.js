include "cfv.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "cun.mm"
include "wss.mm"
include "undif.mm"
include "sylib.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cdm.mm"
include "eqid.mm"
include "csalg.mm"
include "wcel.mm"
include "dmmeasal.mm"
include "saldifcl2.mm"
include "syl3anc.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "a1i.mm"
include "meassre.mm"
include "difssd.mm"
include "meadjunre.mm"
include "eqtr2d.mm"
include "recnd.mm"
include "addrsub.mm"
include "mpbid.mm"

theorem meadif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meadif.m: |- ( ph -> M e. Meas )
  assume meadif.a: |- ( ph -> A e. dom M )
  assume meadif.r: |- ( ph -> ( M ` A ) e. RR )
  assume meadif.b: |- ( ph -> B e. dom M )
  assume meadif.s: |- ( ph -> B C_ A )


  assert |- ( ph -> ( M ` ( A \ B ) ) = ( ( M ` A ) - ( M ` B ) ) )

  proof
    wph
    cB
    cM
    cfv
    #
    cA
    cB
    cdif
    #
    cM
    cfv
    #
    caddc
    co
    #
    cA
    cM
    cfv
    #
    wceq
    @2
    @4
    @0
    cmin
    co
    wceq
    wph
    @4
    cB
    @1
    cun
    #
    cM
    cfv
    @3
    wph
    cA
    @5
    cM
    wph
    @5
    cA
    wph
    cB
    cA
    wss
    @5
    cA
    wceq
    meadif.s
    cB
    cA
    undif
    sylib
    eqcomd
    fveq2d
    wph
    cB
    @1
    cM
    cdm
    #
    cM
    meadif.m
    @6
    eqid
    #
    meadif.b
    wph
    @6
    csalg
    wcel
    cA
    @6
    wcel
    cB
    @6
    wcel
    @1
    @6
    wcel
    wph
    @6
    cM
    meadif.m
    @7
    dmmeasal
    meadif.a
    meadif.b
    @6
    cA
    cB
    saldifcl2
    syl3anc
    #
    cB
    @1
    cin
    c0
    wceq
    wph
    cB
    cA
    disjdif
    a1i
    wph
    cA
    cB
    cM
    meadif.m
    meadif.a
    meadif.r
    meadif.s
    meadif.b
    meassre
    #
    wph
    cA
    @1
    cM
    meadif.m
    meadif.a
    meadif.r
    wph
    cA
    cB
    difssd
    @8
    meassre
    #
    meadjunre
    eqtr2d
    wph
    @0
    @2
    @4
    wph
    @0
    @9
    recnd
    wph
    @2
    @10
    recnd
    wph
    @4
    meadif.r
    recnd
    addrsub
    mpbid
end
