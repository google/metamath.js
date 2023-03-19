include "cqs.mm"
include "cuni.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "cvv.mm"
include "wer.mm"
include "cfn.mm"
include "wcel.mm"
include "erex.mm"
include "sylc.mm"
include "uniqs2.mm"
include "fveq2d.mm"
include "cpw.mm"
include "wss.mm"
include "pwfi.mm"
include "sylib.mm"
include "qsss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "elpwi.mm"
include "ex.mm"
include "syl2im.mm"
include "ssrdv.mm"
include "sstrd.mm"
include "wdisj.mm"
include "qsdisj2.mm"
include "syl.mm"
include "hashuni.mm"
include "eqtr3d.mm"

theorem qshash
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let c.sm: class .~
  assume qshash.1: |- ( ph -> .~ Er A )
  assume qshash.2: |- ( ph -> A e. Fin )

  disjoint A x
  disjoint ph x
  disjoint .~ x
  assert |- ( ph -> ( # ` A ) = sum_ x e. ( A /. .~ ) ( # ` x ) )

  proof
    wph
    cA
    c.sm
    cqs
    #
    cuni
    #
    chash
    cfv
    cA
    chash
    cfv
    @0
    vx
    cv
    #
    chash
    cfv
    vx
    csu
    wph
    @1
    cA
    chash
    wph
    cA
    c.sm
    cvv
    qshash.1
    wph
    cA
    c.sm
    wer
    #
    cA
    cfn
    wcel
    #
    c.sm
    cvv
    wcel
    qshash.1
    qshash.2
    cA
    c.sm
    cfn
    erex
    sylc
    uniqs2
    fveq2d
    wph
    vx
    @0
    wph
    cA
    cpw
    #
    cfn
    wcel
    #
    @0
    @5
    wss
    @0
    cfn
    wcel
    wph
    @4
    @6
    qshash.2
    cA
    pwfi
    sylib
    wph
    cA
    c.sm
    qshash.1
    qsss
    #
    @5
    @0
    ssfi
    syl2anc
    wph
    @0
    @5
    cfn
    @7
    wph
    vx
    @5
    cfn
    wph
    @4
    @2
    @5
    wcel
    @2
    cA
    wss
    #
    @2
    cfn
    wcel
    #
    qshash.2
    @2
    cA
    elpwi
    @4
    @8
    @9
    cA
    @2
    ssfi
    ex
    syl2im
    ssrdv
    sstrd
    wph
    @3
    vx
    @0
    @2
    wdisj
    qshash.1
    vx
    cA
    c.sm
    cA
    qsdisj2
    syl
    hashuni
    eqtr3d
end
