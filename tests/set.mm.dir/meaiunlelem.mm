include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cle.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wdisj.mm"
include "iundjiun.mm"
include "simplrd.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cfzo.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "csalg.mm"
include "dmmeasal.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cfn.mm"
include "fzofi.mm"
include "csdm.mm"
include "isfinite.mm"
include "biimpi.mm"
include "sdomdom.mm"
include "syl.mm"
include "ax-mp.mm"
include "a1i.mm"
include "wf.mm"
include "cuz.mm"
include "elfzouz.mm"
include "eqcomi.mm"
include "syl6eleq.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "saliuncl.mm"
include "saldifcl2.mm"
include "syl3anc.mm"
include "fmptdf.mm"
include "eqid.mm"
include "uzct.mm"
include "eqbrtri.mm"
include "simprd.mm"
include "meadjiun.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cmea.mm"
include "meacl.mm"
include "simpr.mm"
include "difexg.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "difssd.mm"
include "eqsstrd.mm"
include "meassle.mm"
include "sge0lempt.mm"
include "eqbrtrd.mm"

theorem meaiunlelem
  let wph: wff ph
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume meaiunlelem.1: |- F/ n ph
  assume meaiunlelem.m: |- ( ph -> M e. Meas )
  assume meaiunlelem.s: |- S = dom M
  assume meaiunlelem.z: |- Z = ( ZZ>= ` N )
  assume meaiunlelem.e: |- ( ph -> E : Z --> S )
  assume meaiunlelem.f: |- F = ( n e. Z |-> ( ( E ` n ) \ U_ i e. ( N ..^ n ) ( E ` i ) ) )

  disjoint E i
  disjoint E n
  disjoint i n
  disjoint M n
  disjoint N i
  disjoint N n
  disjoint S i
  disjoint S n
  disjoint Z n
  disjoint i ph
  disjoint E x
  disjoint i x
  disjoint n x
  disjoint F x
  disjoint N x
  disjoint Z x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( M ` U_ n e. Z ( E ` n ) ) <_ ( sum^ ` ( n e. Z |-> ( M ` ( E ` n ) ) ) ) )

  proof
    wph
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cM
    cfv
    #
    vn
    cZ
    @0
    cF
    cfv
    #
    cM
    cfv
    #
    cmpt
    csumge0
    cfv
    #
    vn
    cZ
    @1
    cM
    cfv
    #
    cmpt
    csumge0
    cfv
    cle
    wph
    @3
    vn
    cZ
    @4
    ciun
    #
    cM
    cfv
    @6
    @6
    wph
    @2
    @8
    cM
    wph
    @8
    @2
    wph
    vn
    cN
    vx
    cv
    cfz
    co
    #
    @4
    ciun
    vn
    @9
    @1
    ciun
    wceq
    vx
    cZ
    wral
    #
    @8
    @2
    wceq
    #
    vn
    cZ
    @4
    wdisj
    #
    wph
    vi
    vx
    vn
    cE
    cF
    cN
    cS
    cZ
    meaiunlelem.1
    meaiunlelem.z
    meaiunlelem.e
    meaiunlelem.f
    iundjiun
    #
    simplrd
    eqcomd
    fveq2d
    wph
    cZ
    @4
    cS
    vn
    cM
    meaiunlelem.1
    meaiunlelem.m
    meaiunlelem.s
    wph
    cZ
    cS
    @0
    cF
    wph
    vn
    cZ
    @1
    vi
    cN
    @0
    cfzo
    co
    #
    vi
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cdif
    #
    cS
    cF
    meaiunlelem.1
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    cS
    csalg
    wcel
    #
    @1
    cS
    wcel
    #
    @17
    cS
    wcel
    #
    @18
    cS
    wcel
    wph
    @21
    @19
    wph
    cS
    cM
    meaiunlelem.m
    meaiunlelem.s
    dmmeasal
    #
    adantr
    wph
    cZ
    cS
    @0
    cE
    meaiunlelem.e
    ffvelrnda
    #
    wph
    @23
    @19
    wph
    cS
    vi
    @16
    @14
    @24
    @14
    com
    cdom
    wbr
    #
    wph
    @14
    cfn
    wcel
    #
    @26
    cN
    @0
    fzofi
    @27
    @14
    com
    csdm
    wbr
    #
    @26
    @27
    @28
    @14
    isfinite
    biimpi
    @14
    com
    sdomdom
    syl
    ax-mp
    a1i
    wph
    @15
    @14
    wcel
    #
    wa
    cZ
    cS
    @15
    cE
    wph
    cZ
    cS
    cE
    wf
    @29
    meaiunlelem.e
    adantr
    @29
    @15
    cZ
    wcel
    wph
    @29
    @15
    cN
    cuz
    cfv
    #
    cZ
    @15
    cN
    @0
    elfzouz
    cZ
    @30
    meaiunlelem.z
    eqcomi
    syl6eleq
    adantl
    ffvelrnd
    saliuncl
    adantr
    cS
    @1
    @17
    saldifcl2
    syl3anc
    meaiunlelem.f
    fmptdf
    ffvelrnda
    #
    cZ
    com
    cdom
    wbr
    wph
    cZ
    @30
    com
    cdom
    meaiunlelem.z
    cN
    @30
    @30
    eqid
    uzct
    eqbrtri
    a1i
    wph
    @10
    @11
    wa
    @12
    @13
    simprd
    meadjiun
    wph
    @6
    eqidd
    3eqtrd
    wph
    vn
    cZ
    @5
    @7
    cvv
    meaiunlelem.1
    cZ
    cvv
    wcel
    wph
    cZ
    @30
    cvv
    meaiunlelem.z
    cN
    cuz
    fvex
    eqeltri
    a1i
    @20
    @4
    cS
    cM
    wph
    cM
    cmea
    wcel
    @19
    meaiunlelem.m
    adantr
    #
    meaiunlelem.s
    @31
    meacl
    @20
    @1
    cS
    cM
    @32
    meaiunlelem.s
    @25
    meacl
    @20
    @4
    @1
    cS
    cM
    @32
    meaiunlelem.s
    @31
    @25
    @20
    @4
    @18
    @1
    @20
    @19
    @18
    cvv
    wcel
    #
    @4
    @18
    wceq
    wph
    @19
    simpr
    @20
    @22
    @33
    @25
    @1
    @17
    cS
    difexg
    syl
    vn
    cZ
    @18
    cvv
    cF
    meaiunlelem.f
    fvmpt2
    syl2anc
    @20
    @1
    @17
    difssd
    eqsstrd
    meassle
    sge0lempt
    eqbrtrd
end
