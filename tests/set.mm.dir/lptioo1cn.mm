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
include "lptioo1.mm"
include "ctop.mm"
include "cuni.mm"
include "wss.mm"
include "wceq.mm"
include "cnfldtop.mm"
include "a1i.mm"
include "cc.mm"
include "ax-resscn.mm"
include "unicntop.mm"
include "sseqtri.mm"
include "ioossre.mm"
include "tgioo2.mm"
include "restlp.mm"
include "syl3anc.mm"
include "eleqtrd.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "syl6eleq.mm"

theorem lptioo1cn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  assume lptioo1cn.1: |- J = ( TopOpen ` CCfld )
  assume lptioo1cn.2: |- ( ph -> B e. RR* )
  assume lptioo1cn.3: |- ( ph -> A e. RR )
  assume lptioo1cn.4: |- ( ph -> A < B )


  assert |- ( ph -> A e. ( ( limPt ` J ) ` ( A (,) B ) ) )

  proof
    wph
    cA
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
    cA
    @3
    wcel
    #
    cA
    cr
    wcel
    #
    wph
    cA
    @3
    cr
    cin
    #
    wcel
    @5
    @6
    wa
    wph
    cA
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
    lptioo1cn.3
    lptioo1cn.2
    lptioo1cn.4
    lptioo1
    wph
    @1
    ctop
    wcel
    #
    cr
    @1
    cuni
    #
    wss
    #
    @0
    cr
    wss
    #
    @9
    @7
    wceq
    @10
    wph
    @1
    @1
    eqid
    #
    cnfldtop
    a1i
    @12
    wph
    cr
    cc
    @11
    ax-resscn
    unicntop
    sseqtri
    a1i
    @13
    wph
    cA
    cB
    ioossre
    a1i
    @0
    @1
    @8
    @11
    cr
    @11
    eqid
    @1
    @14
    tgioo2
    restlp
    syl3anc
    eleqtrd
    cA
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
    lptioo1cn.1
    eqcomi
    fveq2i
    fveq1i
    syl6eleq
end
