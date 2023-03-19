include "cioo.mm"
include "co.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "clp.mm"
include "wcel.mm"
include "cr.mm"
include "cin.mm"
include "wa.mm"
include "crn.mm"
include "ctg.mm"
include "eqid.mm"
include "lptioo2.mm"
include "ctop.mm"
include "cuni.mm"
include "wss.mm"
include "wceq.mm"
include "cnfldtop.mm"
include "cc.mm"
include "ax-resscn.mm"
include "unicntop.mm"
include "sseqtri.mm"
include "ioossre.mm"
include "tgioo2.mm"
include "restlp.mm"
include "mp3an.mm"
include "syl6eleq.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "fveq1i.mm"

theorem lptioo2cn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  assume lptioo2cn.1: |- J = ( TopOpen ` CCfld )
  assume lptioo2cn.2: |- ( ph -> A e. RR* )
  assume lptioo2cn.3: |- ( ph -> B e. RR )
  assume lptioo2cn.4: |- ( ph -> A < B )


  assert |- ( ph -> B e. ( ( limPt ` J ) ` ( A (,) B ) ) )

  proof
    wph
    cB
    cA
    cB
    cioo
    co
    #
    ccnfld
    ctopn
    cfv
    #
    clp
    cfv
    #
    cfv
    #
    @0
    cJ
    clp
    cfv
    #
    cfv
    wph
    cB
    @3
    wcel
    #
    cB
    cr
    wcel
    #
    wph
    cB
    @3
    cr
    cin
    #
    wcel
    @5
    @6
    wa
    wph
    cB
    @0
    cioo
    crn
    ctg
    cfv
    #
    clp
    cfv
    cfv
    #
    @7
    wph
    cA
    cB
    @8
    @8
    eqid
    lptioo2cn.2
    lptioo2cn.3
    lptioo2cn.4
    lptioo2
    @1
    ctop
    wcel
    cr
    @1
    cuni
    #
    wss
    @0
    cr
    wss
    @9
    @7
    wceq
    @1
    @1
    eqid
    #
    cnfldtop
    cr
    cc
    @10
    ax-resscn
    unicntop
    sseqtri
    cA
    cB
    ioossre
    @0
    @1
    @8
    @10
    cr
    @10
    eqid
    @1
    @11
    tgioo2
    restlp
    mp3an
    syl6eleq
    cB
    @3
    cr
    elin
    sylib
    simpld
    @0
    @2
    @4
    @1
    cJ
    clp
    cJ
    @1
    lptioo2cn.1
    eqcomi
    fveq2i
    fveq1i
    syl6eleq
end
