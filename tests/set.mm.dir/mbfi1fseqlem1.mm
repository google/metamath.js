include "cv.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cfl.mm"
include "cdiv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "wcel.mm"
include "cr.mm"
include "wral.mm"
include "cn.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "ad2antrl.mm"
include "nnred.mm"
include "remulcld.mm"
include "reflcl.mm"
include "syl.mm"
include "nndivred.mm"
include "clt.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "mulge0.mm"
include "syl12anc.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nngt0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"

theorem mbfi1fseqlem1
  let wph: wff ph
  let vy: setvar y
  let vm: setvar m
  let cF: class F
  let cJ: class J
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z
  let cG: class G
  let cA: class A
  assume mbfi1fseq.1: |- ( ph -> F e. MblFn )
  assume mbfi1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume mbfi1fseq.3: |- J = ( m e. NN , y e. RR |-> ( ( |_ ` ( ( F ` y ) x. ( 2 ^ m ) ) ) / ( 2 ^ m ) ) )

  disjoint m y
  disjoint F m
  disjoint F y
  disjoint J m
  disjoint m ph
  disjoint ph y
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m x
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F z
  disjoint G g
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint G x
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint A m
  disjoint A x
  disjoint A y
  assert |- ( ph -> J : ( NN X. RR ) --> ( 0 [,) +oo ) )

  proof
    wph
    vy
    cv
    #
    cF
    cfv
    #
    c2
    vm
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @3
    cdiv
    co
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    vy
    cr
    wral
    vm
    cn
    wral
    cn
    cr
    cxp
    @7
    cJ
    wf
    wph
    @8
    vm
    vy
    cn
    cr
    wph
    @2
    cn
    wcel
    #
    @0
    cr
    wcel
    #
    wa
    #
    wa
    #
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    #
    @8
    @12
    @5
    @3
    @12
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @12
    @1
    @3
    @12
    @1
    cr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @12
    @1
    @7
    wcel
    #
    @16
    @17
    wa
    #
    wph
    cr
    @7
    cF
    wf
    @10
    @18
    @11
    mbfi1fseq.2
    @9
    @10
    simpr
    cr
    @7
    @0
    cF
    ffvelrn
    syl2an
    @1
    elrege0
    sylib
    #
    simpld
    @12
    @3
    @9
    @3
    cn
    wcel
    #
    wph
    @10
    @9
    c2
    cn
    wcel
    @2
    cn0
    wcel
    @21
    2nn
    @2
    nnnn0
    c2
    @2
    nnexpcl
    sylancr
    ad2antrl
    #
    nnred
    #
    remulcld
    #
    @4
    reflcl
    syl
    #
    @22
    nndivred
    @12
    @15
    cc0
    @5
    cle
    wbr
    @3
    cr
    wcel
    #
    cc0
    @3
    clt
    wbr
    @13
    @25
    @12
    @5
    @12
    @14
    cc0
    @4
    cle
    wbr
    #
    @5
    cn0
    wcel
    @24
    @12
    @19
    @26
    cc0
    @3
    cle
    wbr
    @27
    @20
    @23
    @12
    @3
    @12
    @3
    @22
    nnnn0d
    nn0ge0d
    @1
    @3
    mulge0
    syl12anc
    @4
    flge0nn0
    syl2anc
    nn0ge0d
    @23
    @12
    @3
    @22
    nngt0d
    @5
    @3
    divge0
    syl22anc
    @6
    elrege0
    sylanbrc
    ralrimivva
    vm
    vy
    cn
    cr
    @6
    @7
    cJ
    mbfi1fseq.3
    fmpt2
    sylib
end
