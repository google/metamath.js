include "wceq.mm"
include "cpr.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "preq1.mm"
include "dfsn2.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqtrd.mm"
include "mpteq1d.mm"
include "fveq2d.mm"
include "adantl.mm"
include "sge0snmpt.mm"
include "adantr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "xaddid2d.mm"
include "eqcomd.mm"
include "wcel.mm"
include "0xr.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "xleadd1d.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "sge0pr.mm"
include "xaddcld.mm"
include "xrleid.mm"
include "syl.mm"
include "pm2.61dan.mm"

theorem sge0prle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cE: class E
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume sge0prle.a: |- ( ph -> A e. V )
  assume sge0prle.b: |- ( ph -> B e. W )
  assume sge0prle.d: |- ( ph -> D e. ( 0 [,] +oo ) )
  assume sge0prle.e: |- ( ph -> E e. ( 0 [,] +oo ) )
  assume sge0prle.cd: |- ( k = A -> C = D )
  assume sge0prle.ce: |- ( k = B -> C = E )

  disjoint A k
  disjoint B k
  disjoint D k
  disjoint E k
  disjoint V k
  disjoint W k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. { A , B } |-> C ) ) <_ ( D +e E ) )

  proof
    wph
    cA
    cB
    wceq
    #
    vk
    cA
    cB
    cpr
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cD
    cE
    cxad
    co
    #
    cle
    wbr
    wph
    @0
    wa
    #
    @3
    cE
    @4
    cle
    @5
    @3
    vk
    cB
    csn
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cE
    @0
    @3
    @8
    wceq
    wph
    @0
    @2
    @7
    csumge0
    @0
    vk
    @1
    @6
    cC
    @0
    @1
    cB
    cB
    cpr
    #
    @6
    cA
    cB
    cB
    preq1
    @9
    @6
    wceq
    @0
    @6
    @9
    cB
    dfsn2
    eqcomi
    a1i
    eqtrd
    mpteq1d
    fveq2d
    adantl
    wph
    @8
    cE
    wceq
    @0
    wph
    cB
    cC
    cE
    vk
    cW
    sge0prle.b
    sge0prle.e
    sge0prle.ce
    sge0snmpt
    adantr
    eqtrd
    wph
    cE
    @4
    cle
    wbr
    @0
    wph
    cE
    cc0
    cE
    cxad
    co
    #
    @4
    cle
    wph
    @10
    cE
    wph
    cE
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cE
    cc0
    cpnf
    iccssxr
    #
    sge0prle.e
    sseldi
    #
    xaddid2d
    eqcomd
    wph
    cc0
    cD
    cE
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    #
    wph
    @11
    cxr
    cD
    @12
    sge0prle.d
    sseldi
    #
    @13
    wph
    @14
    cpnf
    cxr
    wcel
    #
    cD
    @11
    wcel
    #
    cc0
    cD
    cle
    wbr
    @15
    @17
    wph
    pnfxr
    a1i
    sge0prle.d
    cc0
    cpnf
    cD
    iccgelb
    syl3anc
    xleadd1d
    eqbrtrd
    adantr
    eqbrtrd
    wph
    @0
    wn
    #
    wa
    #
    @3
    @4
    @4
    cle
    @20
    cA
    cB
    cC
    cD
    vk
    cE
    cV
    cW
    wph
    cA
    cV
    wcel
    @19
    sge0prle.a
    adantr
    wph
    cB
    cW
    wcel
    @19
    sge0prle.b
    adantr
    wph
    @18
    @19
    sge0prle.d
    adantr
    wph
    cE
    @11
    wcel
    @19
    sge0prle.e
    adantr
    sge0prle.cd
    sge0prle.ce
    @19
    cA
    cB
    wne
    wph
    cA
    cB
    neqne
    adantl
    sge0pr
    wph
    @4
    @4
    cle
    wbr
    #
    @19
    wph
    @4
    cxr
    wcel
    @21
    wph
    cD
    cE
    @16
    @13
    xaddcld
    @4
    xrleid
    syl
    adantr
    eqbrtrd
    pm2.61dan
end
