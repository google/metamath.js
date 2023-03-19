include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cod.mm"
include "cn0.mm"
include "wb.mm"
include "cfn.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "hashcl.mm"
include "adantl.mm"
include "wn.mm"
include "0nn0.mm"
include "a1i.mm"
include "ifclda.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "zndvds.mm"
include "syl3anc.mm"
include "cgrp.mm"
include "ccyg.mm"
include "cyggrp.mm"
include "syl.mm"
include "eqid.mm"
include "cyggenod2.mm"
include "syl2anc.mm"
include "syl6eqr.mm"
include "breq1d.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "iscyggen.mm"
include "simplbi.mm"
include "c0g.mm"
include "odcong.mm"
include "syl112anc.mm"
include "3bitr2d.mm"

theorem cygznlem1
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vz: setvar z
  let cF: class F
  assume cygzn.b: |- B = ( Base ` G )
  assume cygzn.n: |- N = if ( B e. Fin , ( # ` B ) , 0 )
  assume cygzn.y: |- Y = ( Z/nZ ` N )
  assume cygzn.m: |- .x. = ( .g ` G )
  assume cygzn.l: |- L = ( ZRHom ` Y )
  assume cygzn.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }
  assume cygzn.g: |- ( ph -> G e. CycGrp )
  assume cygzn.x: |- ( ph -> X e. E )

  disjoint n x
  disjoint B n
  disjoint B x
  disjoint G n
  disjoint G x
  disjoint .x. n
  disjoint .x. x
  disjoint Y n
  disjoint Y x
  disjoint L n
  disjoint L x
  disjoint N x
  disjoint X n
  disjoint X x
  disjoint a b
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a z
  disjoint B a
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b z
  disjoint B b
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g z
  disjoint B g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i z
  disjoint B i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j z
  disjoint B j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint B k
  disjoint m n
  disjoint m x
  disjoint m z
  disjoint B m
  disjoint n z
  disjoint x z
  disjoint B z
  disjoint E z
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G m
  disjoint G z
  disjoint M m
  disjoint .x. a
  disjoint .x. j
  disjoint .x. k
  disjoint .x. m
  disjoint .x. z
  disjoint Y a
  disjoint Y b
  disjoint Y g
  disjoint Y i
  disjoint Y j
  disjoint Y m
  disjoint Y z
  disjoint L a
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L m
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint F a
  disjoint F b
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F x
  disjoint F z
  disjoint X a
  disjoint X j
  disjoint X k
  disjoint X m
  disjoint X z
  assert |- ( ( ph /\ ( K e. ZZ /\ M e. ZZ ) ) -> ( ( L ` K ) = ( L ` M ) <-> ( K .x. X ) = ( M .x. X ) ) )

  proof
    wph
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    wa
    #
    cK
    cL
    cfv
    cM
    cL
    cfv
    wceq
    #
    cN
    cK
    cM
    cmin
    co
    #
    cdvds
    wbr
    #
    cX
    cG
    cod
    cfv
    #
    cfv
    #
    @5
    cdvds
    wbr
    #
    cK
    cX
    c.x
    co
    cM
    cX
    c.x
    co
    wceq
    #
    @3
    cN
    cn0
    wcel
    #
    @0
    @1
    @4
    @6
    wb
    wph
    @11
    @2
    wph
    cN
    cB
    cfn
    wcel
    #
    cB
    chash
    cfv
    #
    cc0
    cif
    #
    cn0
    cygzn.n
    wph
    @12
    @13
    cc0
    cn0
    @12
    @13
    cn0
    wcel
    wph
    cB
    hashcl
    adantl
    cc0
    cn0
    wcel
    wph
    @12
    wn
    wa
    0nn0
    a1i
    ifclda
    syl5eqel
    adantr
    wph
    @0
    @1
    simprl
    #
    wph
    @0
    @1
    simprr
    #
    cK
    cM
    cL
    cN
    cY
    cygzn.y
    cygzn.l
    zndvds
    syl3anc
    @3
    @8
    cN
    @5
    cdvds
    wph
    @8
    cN
    wceq
    @2
    wph
    @8
    @14
    cN
    wph
    cG
    cgrp
    wcel
    #
    cX
    cE
    wcel
    #
    @8
    @14
    wceq
    wph
    cG
    ccyg
    wcel
    @17
    cygzn.g
    cG
    cyggrp
    syl
    #
    cygzn.x
    vx
    cB
    c.x
    vn
    cE
    cG
    @7
    cX
    cygzn.b
    cygzn.m
    cygzn.e
    @7
    eqid
    #
    cyggenod2
    syl2anc
    cygzn.n
    syl6eqr
    adantr
    breq1d
    @3
    @17
    cX
    cB
    wcel
    #
    @0
    @1
    @9
    @10
    wb
    wph
    @17
    @2
    @19
    adantr
    wph
    @21
    @2
    wph
    @18
    @21
    cygzn.x
    @18
    @21
    vn
    cz
    vn
    cv
    cX
    c.x
    co
    cmpt
    crn
    cB
    wceq
    vx
    cB
    c.x
    vn
    cE
    cG
    cX
    cygzn.b
    cygzn.m
    cygzn.e
    iscyggen
    simplbi
    syl
    adantr
    @15
    @16
    cX
    c.x
    cG
    cK
    cM
    @7
    cB
    cG
    c0g
    cfv
    #
    cygzn.b
    @20
    cygzn.m
    @22
    eqid
    odcong
    syl112anc
    3bitr2d
end
