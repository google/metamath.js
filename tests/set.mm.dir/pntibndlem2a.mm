include "cv.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cicc.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "nnred.mm"
include "1red.mm"
include "cc0.mm"
include "cioo.mm"
include "ioossre.mm"
include "pntibndlem1.mm"
include "sseldi.mm"
include "remulcld.mm"
include "readdcld.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "biimpa.mm"

theorem pntibndlem2a
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cE: class E
  let cK: class K
  let cL: class L
  let cN: class N
  let cZ: class Z
  let va: setvar a
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let ve: setvar e
  let cM: class M
  let cT: class T
  let cY: class Y
  assume pntibnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntibndlem1.1: |- ( ph -> A e. RR+ )
  assume pntibndlem1.l: |- L = ( ( 1 / 4 ) / ( A + 3 ) )
  assume pntibndlem3.2: |- ( ph -> A. x e. RR+ ( abs ` ( ( R ` x ) / x ) ) <_ A )
  assume pntibndlem3.3: |- ( ph -> B e. RR+ )
  assume pntibndlem3.k: |- K = ( exp ` ( B / ( E / 2 ) ) )
  assume pntibndlem3.c: |- C = ( ( 2 x. B ) + ( log ` 2 ) )
  assume pntibndlem3.4: |- ( ph -> E e. ( 0 (,) 1 ) )
  assume pntibndlem3.6: |- ( ph -> Z e. RR+ )
  assume pntibndlem2.10: |- ( ph -> N e. NN )

  disjoint a u
  disjoint a x
  disjoint E a
  disjoint u x
  disjoint E u
  disjoint E x
  disjoint L u
  disjoint L x
  disjoint N a
  disjoint N u
  disjoint N x
  disjoint A u
  disjoint A x
  disjoint C u
  disjoint C x
  disjoint R u
  disjoint R x
  disjoint Z u
  disjoint Z x
  disjoint ph u
  disjoint a d
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint E d
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint E i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint E j
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint E k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint E m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint E n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint E t
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint E v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint E w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint L n
  disjoint L t
  disjoint L v
  disjoint L z
  disjoint N y
  disjoint N z
  disjoint A v
  disjoint C n
  disjoint C t
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint c d
  disjoint c e
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d e
  disjoint R d
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e m
  disjoint e n
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint R e
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R t
  disjoint R v
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint K m
  disjoint M z
  disjoint T x
  disjoint T y
  disjoint Y z
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z v
  disjoint Z w
  disjoint Z y
  disjoint k ph
  disjoint n ph
  disjoint ph t
  disjoint ph w
  assert |- ( ( ph /\ u e. ( N [,] ( ( 1 + ( L x. E ) ) x. N ) ) ) -> ( u e. RR /\ N <_ u /\ u <_ ( ( 1 + ( L x. E ) ) x. N ) ) )

  proof
    wph
    vu
    cv
    #
    cN
    c1
    cL
    cE
    cmul
    co
    #
    caddc
    co
    #
    cN
    cmul
    co
    #
    cicc
    co
    wcel
    #
    @0
    cr
    wcel
    cN
    @0
    cle
    wbr
    @0
    @3
    cle
    wbr
    w3a
    #
    wph
    cN
    cr
    wcel
    @3
    cr
    wcel
    @4
    @5
    wb
    wph
    cN
    pntibndlem2.10
    nnred
    #
    wph
    @2
    cN
    wph
    c1
    @1
    wph
    1red
    wph
    cL
    cE
    wph
    cc0
    c1
    cioo
    co
    #
    cr
    cL
    cc0
    c1
    ioossre
    #
    wph
    cA
    cR
    cL
    va
    pntibnd.r
    pntibndlem1.1
    pntibndlem1.l
    pntibndlem1
    sseldi
    wph
    @7
    cr
    cE
    @8
    pntibndlem3.4
    sseldi
    remulcld
    readdcld
    @6
    remulcld
    cN
    @3
    @0
    elicc2
    syl2anc
    biimpa
end
