include "cv.mm"
include "cmnf.mm"
include "cioo.mm"
include "co.mm"
include "cres.mm"
include "climc.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "cn.mm"
include "cmul.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "csu.mm"
include "wceq.mm"
include "cpnf.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "fourierdlem106.mm"
include "simpld.mm"
include "n0.mm"
include "sylib.mm"
include "simpr.mm"
include "simprd.mm"
include "adantr.mm"
include "cr.mm"
include "wf.mm"
include "ad2antrr.mm"
include "ad4ant14.mm"
include "cpi.mm"
include "cneg.mm"
include "cdm.mm"
include "cdif.mm"
include "cfn.mm"
include "cc.mm"
include "ccncf.mm"
include "cico.mm"
include "cioc.mm"
include "fourierd.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"

theorem fourier2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cX: class X
  let vr: setvar r
  let vl: setvar l
  let vk: setvar k
  assume fourier2.f: |- ( ph -> F : RR --> RR )
  assume fourier2.t: |- T = ( 2 x. _pi )
  assume fourier2.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourier2.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fourier2.dmdv: |- ( ph -> ( ( -u _pi (,) _pi ) \ dom G ) e. Fin )
  assume fourier2.dvcn: |- ( ph -> G e. ( dom G -cn-> CC ) )
  assume fourier2.rlim: |- ( ( ph /\ x e. ( ( -u _pi [,) _pi ) \ dom G ) ) -> ( ( G |` ( x (,) +oo ) ) limCC x ) =/= (/) )
  assume fourier2.llim: |- ( ( ph /\ x e. ( ( -u _pi (,] _pi ) \ dom G ) ) -> ( ( G |` ( -oo (,) x ) ) limCC x ) =/= (/) )
  assume fourier2.x: |- ( ph -> X e. RR )
  assume fourier2.a: |- A = ( n e. NN0 |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourier2.b: |- B = ( n e. NN |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )

  disjoint A n
  disjoint B n
  disjoint F l
  disjoint F n
  disjoint F r
  disjoint F x
  disjoint l n
  disjoint l r
  disjoint l x
  disjoint n r
  disjoint n x
  disjoint r x
  disjoint G x
  disjoint T n
  disjoint T x
  disjoint X l
  disjoint X n
  disjoint X r
  disjoint X x
  disjoint l ph
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. l e. ( ( F |` ( -oo (,) X ) ) limCC X ) E. r e. ( ( F |` ( X (,) +oo ) ) limCC X ) ( ( ( A ` 0 ) / 2 ) + sum_ n e. NN ( ( ( A ` n ) x. ( cos ` ( n x. X ) ) ) + ( ( B ` n ) x. ( sin ` ( n x. X ) ) ) ) ) = ( ( l + r ) / 2 ) )

  proof
    wph
    vl
    cv
    #
    cF
    cmnf
    cX
    cioo
    co
    cres
    cX
    climc
    co
    #
    wcel
    #
    cc0
    cA
    cfv
    c2
    cdiv
    co
    cn
    vn
    cv
    #
    cA
    cfv
    @3
    cX
    cmul
    co
    #
    ccos
    cfv
    cmul
    co
    @3
    cB
    cfv
    @4
    csin
    cfv
    cmul
    co
    caddc
    co
    vn
    csu
    caddc
    co
    @0
    vr
    cv
    #
    caddc
    co
    c2
    cdiv
    co
    wceq
    #
    vr
    cF
    cX
    cpnf
    cioo
    co
    cres
    cX
    climc
    co
    #
    wrex
    #
    wa
    #
    vl
    wex
    #
    @8
    vl
    @1
    wrex
    wph
    @2
    vl
    wex
    #
    @10
    wph
    @1
    c0
    wne
    #
    @11
    wph
    @12
    @7
    c0
    wne
    #
    wph
    vx
    cT
    cF
    cG
    cX
    fourier2.f
    fourier2.t
    fourier2.per
    fourier2.g
    fourier2.dmdv
    fourier2.dvcn
    fourier2.rlim
    fourier2.llim
    fourier2.x
    fourierdlem106
    #
    simpld
    vl
    @1
    n0
    sylib
    wph
    @2
    @9
    vl
    wph
    @2
    @9
    wph
    @2
    wa
    #
    @2
    @8
    wph
    @2
    simpr
    #
    @15
    @5
    @7
    wcel
    #
    @6
    wa
    #
    vr
    wex
    #
    @8
    @15
    @17
    vr
    wex
    #
    @19
    wph
    @20
    @2
    wph
    @13
    @20
    wph
    @12
    @13
    @14
    simprd
    vr
    @7
    n0
    sylib
    adantr
    @15
    @17
    @18
    vr
    @15
    @17
    @18
    @15
    @17
    wa
    #
    @17
    @6
    @15
    @17
    simpr
    #
    @21
    vx
    cA
    cB
    @5
    cT
    vn
    cF
    cG
    @0
    cX
    wph
    cr
    cr
    cF
    wf
    @2
    @17
    fourier2.f
    ad2antrr
    fourier2.t
    wph
    vx
    cv
    #
    cr
    wcel
    @23
    cT
    caddc
    co
    cF
    cfv
    @23
    cF
    cfv
    wceq
    @2
    @17
    fourier2.per
    ad4ant14
    fourier2.g
    wph
    cpi
    cneg
    #
    cpi
    cioo
    co
    cG
    cdm
    #
    cdif
    cfn
    wcel
    @2
    @17
    fourier2.dmdv
    ad2antrr
    wph
    cG
    @25
    cc
    ccncf
    co
    wcel
    @2
    @17
    fourier2.dvcn
    ad2antrr
    wph
    @23
    @24
    cpi
    cico
    co
    @25
    cdif
    wcel
    cG
    @23
    cpnf
    cioo
    co
    cres
    @23
    climc
    co
    c0
    wne
    @2
    @17
    fourier2.rlim
    ad4ant14
    wph
    @23
    @24
    cpi
    cioc
    co
    @25
    cdif
    wcel
    cG
    cmnf
    @23
    cioo
    co
    cres
    @23
    climc
    co
    c0
    wne
    @2
    @17
    fourier2.llim
    ad4ant14
    wph
    cX
    cr
    wcel
    @2
    @17
    fourier2.x
    ad2antrr
    @15
    @2
    @17
    @16
    adantr
    @22
    fourier2.a
    fourier2.b
    fourierd
    jca
    ex
    eximdv
    mpd
    @6
    vr
    @7
    df-rex
    sylibr
    jca
    ex
    eximdv
    mpd
    @8
    vl
    @1
    df-rex
    sylibr
end
