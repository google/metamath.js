include "climc.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wb.mm"
include "wcel.mm"
include "wi.mm"
include "wn.mm"
include "neqne.mm"
include "wa.mm"
include "cr.mm"
include "wss.mm"
include "adantr.mm"
include "cc.mm"
include "wf.mm"
include "cmnf.mm"
include "cioo.mm"
include "cin.mm"
include "clp.mm"
include "cfv.mm"
include "cpnf.mm"
include "cres.mm"
include "simpr.mm"
include "limclner.mm"
include "nne.mm"
include "sylibr.mm"
include "sylan2.mm"
include "ex.mm"
include "con4d.mm"
include "ctop.mm"
include "crn.mm"
include "ctg.mm"
include "retop.mm"
include "eqeltri.mm"
include "inss2.mm"
include "ioossre.mm"
include "sstri.mm"
include "cuni.mm"
include "uniretop.mm"
include "eqcomi.mm"
include "unieqi.mm"
include "eqtri.mm"
include "lpss.mm"
include "mp2an.mm"
include "sseldi.mm"
include "limcleqr.mm"
include "ne0i.mm"
include "syl.mm"
include "impbid.mm"
include "jca.mm"

theorem limclr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  assume limclr.k: |- K = ( TopOpen ` CCfld )
  assume limclr.a: |- ( ph -> A C_ RR )
  assume limclr.j: |- J = ( topGen ` ran (,) )
  assume limclr.f: |- ( ph -> F : A --> CC )
  assume limclr.lp1: |- ( ph -> B e. ( ( limPt ` J ) ` ( A i^i ( -oo (,) B ) ) ) )
  assume limclr.lp2: |- ( ph -> B e. ( ( limPt ` J ) ` ( A i^i ( B (,) +oo ) ) ) )
  assume limclr.l: |- ( ph -> L e. ( ( F |` ( -oo (,) B ) ) limCC B ) )
  assume limclr.r: |- ( ph -> R e. ( ( F |` ( B (,) +oo ) ) limCC B ) )


  assert |- ( ph -> ( ( ( F limCC B ) =/= (/) <-> L = R ) /\ ( L = R -> L e. ( F limCC B ) ) ) )

  proof
    wph
    cF
    cB
    climc
    co
    #
    c0
    wne
    #
    cL
    cR
    wceq
    #
    wb
    @2
    cL
    @0
    wcel
    #
    wi
    wph
    @1
    @2
    wph
    @2
    @1
    wph
    @2
    wn
    #
    @1
    wn
    #
    @4
    wph
    cL
    cR
    wne
    #
    @5
    cL
    cR
    neqne
    wph
    @6
    wa
    #
    @0
    c0
    wceq
    @5
    @7
    cA
    cB
    cR
    cF
    cJ
    cK
    cL
    limclr.k
    wph
    cA
    cr
    wss
    #
    @6
    limclr.a
    adantr
    limclr.j
    wph
    cA
    cc
    cF
    wf
    #
    @6
    limclr.f
    adantr
    wph
    cB
    cA
    cmnf
    cB
    cioo
    co
    #
    cin
    #
    cJ
    clp
    cfv
    #
    cfv
    #
    wcel
    @6
    limclr.lp1
    adantr
    wph
    cB
    cA
    cB
    cpnf
    cioo
    co
    #
    cin
    @12
    cfv
    wcel
    @6
    limclr.lp2
    adantr
    wph
    cL
    cF
    @10
    cres
    cB
    climc
    co
    wcel
    #
    @6
    limclr.l
    adantr
    wph
    cR
    cF
    @14
    cres
    cB
    climc
    co
    wcel
    #
    @6
    limclr.r
    adantr
    wph
    @6
    simpr
    limclner
    @0
    c0
    nne
    sylibr
    sylan2
    ex
    con4d
    wph
    @2
    @1
    wph
    @2
    wa
    #
    @3
    @1
    @17
    cA
    cB
    cR
    cF
    cJ
    cK
    cL
    limclr.k
    wph
    @8
    @2
    limclr.a
    adantr
    limclr.j
    wph
    @9
    @2
    limclr.f
    adantr
    wph
    cB
    cr
    wcel
    @2
    wph
    @13
    cr
    cB
    cJ
    ctop
    wcel
    @11
    cr
    wss
    @13
    cr
    wss
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    limclr.j
    retop
    eqeltri
    @11
    @10
    cr
    cA
    @10
    inss2
    cmnf
    cB
    ioossre
    sstri
    @11
    cJ
    cr
    cr
    @18
    cuni
    cJ
    cuni
    uniretop
    @18
    cJ
    cJ
    @18
    limclr.j
    eqcomi
    unieqi
    eqtri
    lpss
    mp2an
    limclr.lp1
    sseldi
    adantr
    wph
    @15
    @2
    limclr.l
    adantr
    wph
    @16
    @2
    limclr.r
    adantr
    wph
    @2
    simpr
    limcleqr
    #
    @0
    cL
    ne0i
    syl
    ex
    impbid
    wph
    @2
    @3
    @19
    ex
    jca
end
