include "cn.mm"
include "wceq.mm"
include "ciun.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "simpr.mm"
include "iuneq1d.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wral.mm"
include "adantr.mm"
include "ralrimiva.mm"
include "raleqdv.mm"
include "mpbid.mm"
include "sigaclcu2.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "sigaclfu2.mm"
include "mpjaodan.mm"

theorem sigaclcu3
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x
  assume sigaclcu3.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume sigaclcu3.2: |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) )
  assume sigaclcu3.3: |- ( ( ph /\ k e. N ) -> A e. S )

  disjoint S k
  disjoint N k
  disjoint M k
  disjoint k ph
  disjoint o s
  disjoint o x
  disjoint S o
  disjoint s x
  disjoint S s
  disjoint S x
  disjoint A x
  disjoint k x
  assert |- ( ph -> U_ k e. N A e. S )

  proof
    wph
    cN
    cn
    wceq
    #
    vk
    cN
    cA
    ciun
    #
    cS
    wcel
    cN
    c1
    cM
    cfzo
    co
    #
    wceq
    #
    wph
    @0
    wa
    #
    @1
    vk
    cn
    cA
    ciun
    #
    cS
    @4
    vk
    cN
    cn
    cA
    wph
    @0
    simpr
    #
    iuneq1d
    @4
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    wcel
    #
    vk
    cn
    wral
    #
    @5
    cS
    wcel
    wph
    @7
    @0
    sigaclcu3.1
    adantr
    @4
    @8
    vk
    cN
    wral
    #
    @9
    wph
    @10
    @0
    wph
    @8
    vk
    cN
    sigaclcu3.3
    ralrimiva
    #
    adantr
    @4
    @8
    vk
    cN
    cn
    @6
    raleqdv
    mpbid
    cA
    cS
    vk
    sigaclcu2
    syl2anc
    eqeltrd
    wph
    @3
    wa
    #
    @1
    vk
    @2
    cA
    ciun
    #
    cS
    @12
    vk
    cN
    @2
    cA
    wph
    @3
    simpr
    #
    iuneq1d
    @12
    @7
    @8
    vk
    @2
    wral
    #
    @13
    cS
    wcel
    wph
    @7
    @3
    sigaclcu3.1
    adantr
    @12
    @10
    @15
    wph
    @10
    @3
    @11
    adantr
    @12
    @8
    vk
    cN
    @2
    @14
    raleqdv
    mpbid
    cA
    cS
    vk
    cM
    sigaclfu2
    syl2anc
    eqeltrd
    sigaclcu3.2
    mpjaodan
end
