include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "cicc.mm"
include "cima.mm"
include "wss.mm"
include "cico.mm"
include "cc.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cr.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sselda.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "abscld.mm"
include "absge0d.mm"
include "crp.mm"
include "simp2d.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0re.mm"
include "simp1d.mm"
include "rpxrd.mm"
include "elico2.mm"
include "sylancr.mm"
include "mpbir3and.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "wceq.mm"
include "eqid.mm"
include "cnbl0.mm"
include "syl.mm"
include "eleqtrd.mm"
include "icossicc.mm"
include "imass2.mm"
include "mp1i.mm"
include "eqsstr3d.mm"
include "cpnf.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "adantr.mm"
include "sseldi.mm"
include "simp3d.mm"
include "df-ico.mm"
include "df-icc.mm"
include "xrlelttr.mm"
include "ixxss2.mm"
include "syl2anc.mm"
include "syl6sseqr.mm"
include "3jca.mm"

theorem psercnlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let vr: setvar r
  let va: setvar a
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  let vi: setvar i
  let cH: class H
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  assume pserf.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume pserf.f: |- F = ( y e. S |-> sum_ j e. NN0 ( ( G ` y ) ` j ) )
  assume pserf.a: |- ( ph -> A : NN0 --> CC )
  assume pserf.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume psercn.s: |- S = ( `' abs " ( 0 [,) R ) )
  assume psercnlem2.i: |- ( ( ph /\ a e. S ) -> ( M e. RR+ /\ ( abs ` a ) < M /\ M < R ) )

  disjoint a j
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint M j
  disjoint M y
  disjoint G j
  disjoint G r
  disjoint G y
  disjoint S a
  disjoint S j
  disjoint S y
  disjoint F a
  disjoint a ph
  disjoint j ph
  disjoint ph y
  disjoint a k
  disjoint a m
  disjoint a s
  disjoint a w
  disjoint a z
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint H f
  disjoint i j
  disjoint i y
  disjoint H i
  disjoint H j
  disjoint H y
  disjoint i k
  disjoint i m
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i z
  disjoint M i
  disjoint j u
  disjoint j v
  disjoint k u
  disjoint k v
  disjoint M k
  disjoint m u
  disjoint m v
  disjoint M m
  disjoint s u
  disjoint s v
  disjoint M s
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint i x
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint i r
  disjoint G i
  disjoint G k
  disjoint G m
  disjoint G s
  disjoint G w
  disjoint G z
  disjoint a f
  disjoint a i
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f z
  disjoint S f
  disjoint S i
  disjoint S k
  disjoint S m
  disjoint S w
  disjoint S z
  disjoint F f
  disjoint F z
  disjoint f ph
  disjoint i ph
  disjoint k ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- ( ( ph /\ a e. S ) -> ( a e. ( 0 ( ball ` ( abs o. - ) ) M ) /\ ( 0 ( ball ` ( abs o. - ) ) M ) C_ ( `' abs " ( 0 [,] M ) ) /\ ( `' abs " ( 0 [,] M ) ) C_ S ) )

  proof
    wph
    va
    cv
    #
    cS
    wcel
    #
    wa
    #
    @0
    cc0
    cM
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    wcel
    @4
    cabs
    ccnv
    #
    cc0
    cM
    cicc
    co
    #
    cima
    #
    wss
    @7
    cS
    wss
    @2
    @0
    @5
    cc0
    cM
    cico
    co
    #
    cima
    #
    @4
    @2
    @0
    cc
    wcel
    #
    @0
    cabs
    cfv
    #
    @8
    wcel
    #
    @0
    @9
    wcel
    #
    wph
    cS
    cc
    @0
    cS
    cc
    wss
    wph
    cS
    @5
    cc0
    cR
    cico
    co
    #
    cima
    #
    cc
    psercn.s
    @15
    cabs
    cdm
    cc
    cabs
    @14
    cnvimass
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    eqsstri
    a1i
    sselda
    #
    @2
    @12
    @11
    cr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    @11
    cM
    clt
    wbr
    #
    @2
    @0
    @16
    abscld
    @2
    @0
    @16
    absge0d
    @2
    cM
    crp
    wcel
    #
    @19
    cM
    cR
    clt
    wbr
    #
    psercnlem2.i
    simp2d
    @2
    cc0
    cr
    wcel
    cM
    cxr
    wcel
    #
    @12
    @17
    @18
    @19
    w3a
    wb
    0re
    @2
    cM
    @2
    @20
    @19
    @21
    psercnlem2.i
    simp1d
    rpxrd
    #
    cc0
    cM
    @11
    elico2
    sylancr
    mpbir3and
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @13
    @10
    @12
    wa
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    @0
    @8
    cabs
    elpreima
    mp2b
    sylanbrc
    @2
    @22
    @9
    @4
    wceq
    @23
    @3
    cM
    @3
    eqid
    cnbl0
    syl
    #
    eleqtrd
    @2
    @4
    @9
    @7
    @24
    @8
    @6
    wss
    @9
    @7
    wss
    @2
    cc0
    cM
    icossicc
    @8
    @6
    @5
    imass2
    mp1i
    eqsstr3d
    @2
    @7
    @15
    cS
    @2
    @6
    @14
    wss
    #
    @7
    @15
    wss
    @2
    cR
    cxr
    wcel
    @21
    @25
    @2
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cR
    cc0
    cpnf
    iccssxr
    wph
    cR
    @26
    wcel
    @1
    wph
    vx
    cA
    cR
    vn
    cG
    vr
    pserf.g
    pserf.a
    pserf.r
    radcnvcl
    adantr
    sseldi
    @2
    @20
    @19
    @21
    psercnlem2.i
    simp3d
    vu
    vv
    vw
    vz
    cc0
    cM
    cR
    cicc
    cle
    clt
    cle
    cico
    clt
    vu
    vv
    vw
    df-ico
    vu
    vv
    vw
    df-icc
    vz
    cv
    cM
    cR
    xrlelttr
    ixxss2
    syl2anc
    @6
    @14
    @5
    imass2
    syl
    psercn.s
    syl6sseqr
    3jca
end
