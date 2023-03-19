include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmbf.mm"
include "cc.mm"
include "culm.mm"
include "wbr.mm"
include "wf.mm"
include "ulmcl.mm"
include "syl.mm"
include "feqmptd.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cz.mm"
include "adantr.mm"
include "cmap.mm"
include "co.mm"
include "wfn.mm"
include "ffn.mm"
include "ulmf2.mm"
include "syl2anc.mm"
include "simpr.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "adantl.mm"
include "ulmclm.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "eqeltrrd.mm"
include "anasss.mm"
include "mbflim.mm"
include "eqeltrd.mm"

theorem mbfulm
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  assume mbfulm.z: |- Z = ( ZZ>= ` M )
  assume mbfulm.m: |- ( ph -> M e. ZZ )
  assume mbfulm.f: |- ( ph -> F : Z --> MblFn )
  assume mbfulm.u: |- ( ph -> F ( ~~>u ` S ) G )


  assert |- ( ph -> G e. MblFn )

  proof
    wph
    cG
    vz
    cS
    vz
    cv
    #
    cG
    cfv
    #
    cmpt
    cmbf
    wph
    vz
    cS
    cc
    cG
    wph
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    cS
    cc
    cG
    wf
    mbfulm.u
    cS
    cF
    cG
    ulmcl
    syl
    feqmptd
    wph
    vz
    cS
    @0
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @1
    vk
    cM
    cc
    cZ
    mbfulm.z
    mbfulm.m
    wph
    @0
    cS
    wcel
    #
    wa
    #
    @0
    cS
    vn
    cF
    cG
    vk
    cZ
    @5
    cmpt
    #
    cM
    cvv
    cZ
    mbfulm.z
    wph
    cM
    cz
    wcel
    @6
    mbfulm.m
    adantr
    wph
    cZ
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    @6
    wph
    cF
    cZ
    wfn
    #
    @2
    @10
    wph
    cZ
    cmbf
    cF
    wf
    @11
    mbfulm.f
    cZ
    cmbf
    cF
    ffn
    syl
    mbfulm.u
    cS
    cF
    cG
    cZ
    ulmf2
    syl2anc
    #
    adantr
    wph
    @6
    simpr
    @8
    cvv
    wcel
    @7
    vk
    cZ
    @5
    cZ
    cM
    cuz
    cfv
    cvv
    mbfulm.z
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    vn
    cv
    #
    cZ
    wcel
    #
    @0
    @13
    cF
    cfv
    #
    cfv
    #
    @13
    @8
    cfv
    #
    wceq
    @7
    @14
    @17
    @16
    vk
    @13
    @5
    @16
    cZ
    @8
    @3
    @13
    wceq
    @0
    @4
    @15
    @3
    @13
    cF
    fveq2
    fveq1d
    @8
    eqid
    @0
    @15
    fvex
    fvmpt
    eqcomd
    adantl
    wph
    @2
    @6
    mbfulm.u
    adantr
    ulmclm
    wph
    @3
    cZ
    wcel
    #
    wa
    #
    @4
    vz
    cS
    @5
    cmpt
    cmbf
    @19
    vz
    cS
    cc
    @4
    @19
    @4
    @9
    wcel
    cS
    cc
    @4
    wf
    wph
    cZ
    @9
    @3
    cF
    @12
    ffvelrnda
    @4
    cc
    cS
    elmapi
    syl
    #
    feqmptd
    wph
    cZ
    cmbf
    @3
    cF
    mbfulm.f
    ffvelrnda
    eqeltrrd
    wph
    @18
    @6
    @5
    cc
    wcel
    @19
    cS
    cc
    @0
    @4
    @20
    ffvelrnda
    anasss
    mbflim
    eqeltrd
end
