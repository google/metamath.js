include "cmpt.mm"
include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "nfmpt1.mm"
include "fmptd2f.mm"
include "limsupreuz.mm"
include "nfv.mm"
include "nfan.mm"
include "wceq.mm"
include "simpll.mm"
include "uztrn2.mm"
include "adantll.mm"
include "eqid.mm"
include "a1i.mm"
include "fvmpt2d.mm"
include "syl2anc.mm"
include "breq2d.mm"
include "rexbida.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "wb.mm"
include "breq1.mm"
include "ralbidv.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "cbvralv.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "breq1d.mm"
include "ralbida.mm"
include "breq2.mm"
include "anbi12d.mm"

theorem limsupreuzmpt
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vy: setvar y
  assume limsupreuzmpt.j: |- F/ j ph
  assume limsupreuzmpt.m: |- ( ph -> M e. ZZ )
  assume limsupreuzmpt.z: |- Z = ( ZZ>= ` M )
  assume limsupreuzmpt.b: |- ( ( ph /\ j e. Z ) -> B e. RR )

  disjoint B k
  disjoint B x
  disjoint k x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j x
  disjoint B i
  disjoint B y
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint k y
  disjoint x y
  disjoint Z i
  disjoint Z y
  disjoint i j
  disjoint j y
  disjoint i ph
  disjoint ph y
  assert |- ( ph -> ( ( limsup ` ( j e. Z |-> B ) ) e. RR <-> ( E. x e. RR A. k e. Z E. j e. ( ZZ>= ` k ) x <_ B /\ E. x e. RR A. j e. Z B <_ x ) ) )

  proof
    wph
    vj
    cZ
    cB
    cmpt
    #
    clsp
    cfv
    cr
    wcel
    vy
    cv
    #
    vj
    cv
    #
    @0
    cfv
    #
    cle
    wbr
    #
    vj
    vi
    cv
    #
    cuz
    cfv
    #
    wrex
    #
    vi
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @3
    @1
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    wa
    vx
    cv
    #
    cB
    cle
    wbr
    #
    vj
    vk
    cv
    #
    cuz
    cfv
    #
    wrex
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    cB
    @13
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    wa
    wph
    vy
    vj
    vi
    @0
    cM
    cZ
    vj
    cZ
    cB
    nfmpt1
    limsupreuzmpt.m
    limsupreuzmpt.z
    wph
    vj
    cZ
    cB
    cr
    limsupreuzmpt.j
    limsupreuzmpt.b
    fmptd2f
    limsupreuz
    wph
    @9
    @19
    @12
    @22
    wph
    @9
    @1
    cB
    cle
    wbr
    #
    vj
    @6
    wrex
    #
    vi
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @19
    wph
    @8
    @25
    vy
    cr
    wph
    @7
    @24
    vi
    cZ
    wph
    @5
    cZ
    wcel
    #
    wa
    #
    @4
    @23
    vj
    @6
    wph
    @27
    vj
    limsupreuzmpt.j
    @27
    vj
    nfv
    nfan
    @28
    @2
    @6
    wcel
    #
    wa
    #
    @3
    cB
    @1
    cle
    @30
    wph
    @2
    cZ
    wcel
    #
    @3
    cB
    wceq
    wph
    @27
    @29
    simpll
    @27
    @29
    @31
    wph
    cM
    @2
    @5
    cZ
    limsupreuzmpt.z
    uztrn2
    adantll
    wph
    vj
    cZ
    cB
    @0
    cr
    @0
    @0
    wceq
    wph
    @0
    eqid
    a1i
    limsupreuzmpt.b
    fvmpt2d
    #
    syl2anc
    breq2d
    rexbida
    ralbidva
    rexbidv
    @26
    @19
    wb
    wph
    @25
    @18
    vy
    vx
    cr
    @1
    @13
    wceq
    #
    @25
    @14
    vj
    @6
    wrex
    #
    vi
    cZ
    wral
    #
    @18
    @33
    @24
    @34
    vi
    cZ
    @33
    @23
    @14
    vj
    @6
    @1
    @13
    cB
    cle
    breq1
    rexbidv
    ralbidv
    @35
    @18
    wb
    @33
    @34
    @17
    vi
    vk
    cZ
    @5
    @15
    wceq
    @14
    vj
    @6
    @16
    @5
    @15
    cuz
    fveq2
    rexeqdv
    cbvralv
    a1i
    bitrd
    cbvrexv
    a1i
    bitrd
    wph
    @12
    cB
    @1
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @22
    wph
    @11
    @37
    vy
    cr
    wph
    @10
    @36
    vj
    cZ
    limsupreuzmpt.j
    wph
    @31
    wa
    @3
    cB
    @1
    cle
    @32
    breq1d
    ralbida
    rexbidv
    @38
    @22
    wb
    wph
    @37
    @21
    vy
    vx
    cr
    @33
    @36
    @20
    vj
    cZ
    @1
    @13
    cB
    cle
    breq2
    ralbidv
    cbvrexv
    a1i
    bitrd
    anbi12d
    bitrd
end
