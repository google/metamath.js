include "cdgr.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cn0.mm"
include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "dgrle.mm"
include "cply.mm"
include "ccoe.mm"
include "wne.mm"
include "coeeq.mm"
include "fveq1d.mm"
include "eqnetrd.mm"
include "eqid.mm"
include "dgrub.mm"
include "syl3anc.mm"
include "dgrcl.mm"
include "syl.mm"
include "nn0red.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem dgreq
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  assume dgreq.1: |- ( ph -> F e. ( Poly ` S ) )
  assume dgreq.2: |- ( ph -> N e. NN0 )
  assume dgreq.3: |- ( ph -> A : NN0 --> CC )
  assume dgreq.4: |- ( ph -> ( A " ( ZZ>= ` ( N + 1 ) ) ) = { 0 } )
  assume dgreq.5: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( z ^ k ) ) ) )
  assume dgreq.6: |- ( ph -> ( A ` N ) =/= 0 )

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint N k
  disjoint N z
  disjoint k ph
  disjoint ph z
  assert |- ( ph -> ( deg ` F ) = N )

  proof
    wph
    cF
    cdgr
    cfv
    #
    cN
    wceq
    @0
    cN
    cle
    wbr
    cN
    @0
    cle
    wbr
    #
    wph
    vz
    vk
    cv
    #
    cA
    cfv
    #
    cS
    vk
    cF
    cN
    dgreq.1
    dgreq.2
    wph
    cn0
    cc
    cA
    wf
    @2
    cn0
    wcel
    @3
    cc
    wcel
    @2
    cc0
    cN
    cfz
    co
    wcel
    dgreq.3
    @2
    cN
    elfznn0
    cn0
    cc
    @2
    cA
    ffvelrn
    syl2an
    dgreq.5
    dgrle
    wph
    cF
    cS
    cply
    cfv
    wcel
    #
    cN
    cn0
    wcel
    cN
    cF
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    @1
    dgreq.1
    dgreq.2
    wph
    @6
    cN
    cA
    cfv
    cc0
    wph
    cN
    @5
    cA
    wph
    vz
    cA
    cS
    vk
    cF
    cN
    dgreq.1
    dgreq.2
    dgreq.3
    dgreq.4
    dgreq.5
    coeeq
    fveq1d
    dgreq.6
    eqnetrd
    @5
    cS
    cF
    cN
    @0
    @5
    eqid
    @0
    eqid
    dgrub
    syl3anc
    wph
    @0
    cN
    wph
    @0
    wph
    @4
    @0
    cn0
    wcel
    dgreq.1
    cS
    cF
    dgrcl
    syl
    nn0red
    wph
    cN
    dgreq.2
    nn0red
    letri3d
    mpbir2and
end
