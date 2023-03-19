include "citg2.mm"
include "cfv.mm"
include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "citg1.mm"
include "cdm.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cico.mm"
include "wss.mm"
include "icossicc.mm"
include "fss.mm"
include "sylancl.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "itg2i1fseqle.mm"
include "itg2ub.mm"
include "syl3anc.mm"
include "itg2i1fseq2.mm"

theorem itg2i1fseq3
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume itg2i1fseq.1: |- ( ph -> F e. MblFn )
  assume itg2i1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2i1fseq.3: |- ( ph -> P : NN --> dom S.1 )
  assume itg2i1fseq.4: |- ( ph -> A. n e. NN ( 0p oR <_ ( P ` n ) /\ ( P ` n ) oR <_ ( P ` ( n + 1 ) ) ) )
  assume itg2i1fseq.5: |- ( ph -> A. x e. RR ( n e. NN |-> ( ( P ` n ) ` x ) ) ~~> ( F ` x ) )
  assume itg2i1fseq.6: |- S = ( m e. NN |-> ( S.1 ` ( P ` m ) ) )
  assume itg2i1fseq3.7: |- ( ph -> ( S.2 ` F ) e. RR )

  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint P m
  disjoint P n
  disjoint P x
  disjoint m ph
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint M k
  disjoint M n
  disjoint M y
  disjoint M z
  disjoint P k
  disjoint P y
  disjoint P z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  disjoint S k
  disjoint S y
  disjoint S z
  assert |- ( ph -> S ~~> ( S.2 ` F ) )

  proof
    wph
    vx
    cP
    cS
    vk
    vm
    vn
    cF
    cF
    citg2
    cfv
    #
    itg2i1fseq.1
    itg2i1fseq.2
    itg2i1fseq.3
    itg2i1fseq.4
    itg2i1fseq.5
    itg2i1fseq.6
    itg2i1fseq3.7
    wph
    vk
    cv
    #
    cn
    wcel
    #
    wa
    cr
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @1
    cP
    cfv
    #
    citg1
    cdm
    #
    wcel
    @5
    cF
    cle
    cofr
    wbr
    @5
    citg1
    cfv
    @0
    cle
    wbr
    wph
    @4
    @2
    wph
    cr
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    @7
    @3
    wss
    @4
    itg2i1fseq.2
    cc0
    cpnf
    icossicc
    cr
    @7
    @3
    cF
    fss
    sylancl
    adantr
    wph
    cn
    @6
    @1
    cP
    itg2i1fseq.3
    ffvelrnda
    wph
    vx
    cP
    vn
    cF
    @1
    itg2i1fseq.1
    itg2i1fseq.2
    itg2i1fseq.3
    itg2i1fseq.4
    itg2i1fseq.5
    itg2i1fseqle
    cF
    @5
    itg2ub
    syl3anc
    itg2i1fseq2
end
