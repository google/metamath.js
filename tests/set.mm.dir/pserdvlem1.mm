include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "crp.mm"
include "clt.mm"
include "wbr.mm"
include "cc.mm"
include "wss.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cr.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sselda.mm"
include "abscld.mm"
include "psercnlem1.mm"
include "simp1d.mm"
include "rpred.mm"
include "readdcld.mm"
include "0red.mm"
include "absge0d.mm"
include "ltaddrpd.mm"
include "lelttrd.mm"
include "elrpd.mm"
include "rphalfcld.mm"
include "simp2d.mm"
include "wb.mm"
include "avglt1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "rehalfcld.mm"
include "rexrd.mm"
include "cxr.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "sseldi.mm"
include "adantr.mm"
include "avglt2.mm"
include "simp3d.mm"
include "xrlttrd.mm"
include "3jca.mm"

theorem pserdvlem1
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
  assume psercn.m: |- M = if ( R e. RR , ( ( ( abs ` a ) + R ) / 2 ) , ( ( abs ` a ) + 1 ) )

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
  assert |- ( ( ph /\ a e. S ) -> ( ( ( ( abs ` a ) + M ) / 2 ) e. RR+ /\ ( abs ` a ) < ( ( ( abs ` a ) + M ) / 2 ) /\ ( ( ( abs ` a ) + M ) / 2 ) < R ) )

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
    cabs
    cfv
    #
    cM
    caddc
    co
    #
    c2
    cdiv
    co
    #
    crp
    wcel
    @3
    @5
    clt
    wbr
    #
    @5
    cR
    clt
    wbr
    @2
    @4
    @2
    @4
    @2
    @3
    cM
    @2
    @0
    wph
    cS
    cc
    @0
    cS
    cc
    wss
    wph
    cS
    cabs
    ccnv
    cc0
    cR
    cico
    co
    #
    cima
    #
    cc
    psercn.s
    @8
    cabs
    cdm
    cc
    cabs
    @7
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
    abscld
    #
    @2
    cM
    @2
    cM
    crp
    wcel
    #
    @3
    cM
    clt
    wbr
    #
    cM
    cR
    clt
    wbr
    #
    wph
    vx
    vy
    cA
    cR
    cS
    vj
    vn
    cF
    cG
    cM
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    psercn.m
    psercnlem1
    #
    simp1d
    #
    rpred
    #
    readdcld
    #
    @2
    cc0
    @3
    @4
    @2
    0red
    @10
    @17
    @2
    @0
    @9
    absge0d
    @2
    @3
    cM
    @10
    @15
    ltaddrpd
    lelttrd
    elrpd
    rphalfcld
    @2
    @12
    @6
    @2
    @11
    @12
    @13
    @14
    simp2d
    #
    @2
    @3
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @12
    @6
    wb
    @10
    @16
    @3
    cM
    avglt1
    syl2anc
    mpbid
    @2
    @5
    cM
    cR
    @2
    @5
    @2
    @4
    @17
    rehalfcld
    rexrd
    @2
    cM
    @16
    rexrd
    wph
    cR
    cxr
    wcel
    @1
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cR
    cc0
    cpnf
    iccssxr
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
    sseldi
    adantr
    @2
    @12
    @5
    cM
    clt
    wbr
    #
    @18
    @2
    @19
    @20
    @12
    @21
    wb
    @10
    @16
    @3
    cM
    avglt2
    syl2anc
    mpbid
    @2
    @11
    @12
    @13
    @14
    simp3d
    xrlttrd
    3jca
end
