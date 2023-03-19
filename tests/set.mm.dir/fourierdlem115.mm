include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cc0.mm"
include "cfv.mm"
include "cmin.mm"
include "cli.mm"
include "wbr.mm"
include "cn.mm"
include "cv.mm"
include "cmul.mm"
include "ccos.mm"
include "csin.mm"
include "csu.mm"
include "wceq.mm"
include "cpi.mm"
include "cneg.mm"
include "wa.mm"
include "clt.mm"
include "cfzo.mm"
include "wral.mm"
include "cr.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "cfl.mm"
include "ctp.mm"
include "cicc.mm"
include "cdm.mm"
include "cdif.mm"
include "cun.mm"
include "chash.mm"
include "wiso.mm"
include "cio.mm"
include "cn0.mm"
include "cioo.mm"
include "citg.mm"
include "wcel.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "adantr.mm"
include "itgeq2dv.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "eqid.mm"
include "id.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "isoeq1.mm"
include "cbviotav.mm"
include "fourierdlem114.mm"
include "simpld.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfov.mm"
include "fveq2.mm"
include "cbvsumi.mm"
include "oveq2i.mm"
include "simprd.mm"
include "syl5eq.mm"
include "jca.mm"

theorem fourierdlem115
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cL: class L
  let cX: class X
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  let vy: setvar y
  assume fourierdlem115.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem115.t: |- T = ( 2 x. _pi )
  assume fourierdlem115.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem115.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fourierdlem115.dmdv: |- ( ph -> ( ( -u _pi (,) _pi ) \ dom G ) e. Fin )
  assume fourierdlem115.dvcn: |- ( ph -> G e. ( dom G -cn-> CC ) )
  assume fourierdlem115.rlim: |- ( ( ph /\ x e. ( ( -u _pi [,) _pi ) \ dom G ) ) -> ( ( G |` ( x (,) +oo ) ) limCC x ) =/= (/) )
  assume fourierdlem115.llim: |- ( ( ph /\ x e. ( ( -u _pi (,] _pi ) \ dom G ) ) -> ( ( G |` ( -oo (,) x ) ) limCC x ) =/= (/) )
  assume fourierdlem115.x: |- ( ph -> X e. RR )
  assume fourierdlem115.l: |- ( ph -> L e. ( ( F |` ( -oo (,) X ) ) limCC X ) )
  assume fourierdlem115.r: |- ( ph -> R e. ( ( F |` ( X (,) +oo ) ) limCC X ) )
  assume fourierdlem115.a: |- A = ( n e. NN0 |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierdlem115.b: |- B = ( n e. NN |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierdlem115.s: |- S = ( k e. NN |-> ( ( ( A ` k ) x. ( cos ` ( k x. X ) ) ) + ( ( B ` k ) x. ( sin ` ( k x. X ) ) ) ) )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint F n
  disjoint F x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint G k
  disjoint G x
  disjoint L k
  disjoint R k
  disjoint T k
  disjoint T x
  disjoint X k
  disjoint X n
  disjoint X x
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint F z
  disjoint k z
  disjoint x z
  disjoint G f
  disjoint G g
  disjoint f g
  disjoint G w
  disjoint G z
  disjoint g k
  disjoint g w
  disjoint g z
  disjoint k w
  disjoint w z
  disjoint g x
  disjoint L z
  disjoint R z
  disjoint T f
  disjoint T g
  disjoint T y
  disjoint f y
  disjoint g y
  disjoint T w
  disjoint T z
  disjoint k y
  disjoint w y
  disjoint y z
  disjoint x y
  disjoint X f
  disjoint X g
  disjoint X w
  disjoint X z
  disjoint f ph
  disjoint ph z
  assert |- ( ph -> ( seq 1 ( + , S ) ~~> ( ( ( L + R ) / 2 ) - ( ( A ` 0 ) / 2 ) ) /\ ( ( ( A ` 0 ) / 2 ) + sum_ n e. NN ( ( ( A ` n ) x. ( cos ` ( n x. X ) ) ) + ( ( B ` n ) x. ( sin ` ( n x. X ) ) ) ) ) = ( ( L + R ) / 2 ) ) )

  proof
    wph
    caddc
    cS
    c1
    cseq
    cL
    cR
    caddc
    co
    c2
    cdiv
    co
    #
    cc0
    cA
    cfv
    c2
    cdiv
    co
    #
    cmin
    co
    cli
    wbr
    #
    @1
    cn
    vn
    cv
    #
    cA
    cfv
    #
    @3
    cX
    cmul
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    @3
    cB
    cfv
    #
    @5
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    vn
    csu
    #
    caddc
    co
    #
    @0
    wceq
    wph
    @2
    @1
    cn
    vk
    cv
    #
    cA
    cfv
    #
    @14
    cX
    cmul
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    @14
    cB
    cfv
    #
    @16
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    vk
    csu
    #
    caddc
    co
    #
    @0
    wceq
    #
    wph
    vx
    cA
    cB
    vk
    cn
    cc0
    vw
    cv
    #
    cfv
    cpi
    cneg
    #
    wceq
    @14
    @26
    cfv
    cpi
    wceq
    wa
    vz
    cv
    #
    @26
    cfv
    @28
    c1
    caddc
    co
    @26
    cfv
    clt
    wbr
    vz
    cc0
    @14
    cfzo
    co
    wral
    wa
    vw
    cr
    cc0
    @14
    cfz
    co
    cmap
    co
    crab
    cmpt
    #
    cc0
    @27
    cpi
    cX
    vy
    cr
    vy
    cv
    #
    cpi
    @30
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    cfv
    ctp
    @27
    cpi
    cicc
    co
    cG
    cdm
    cdif
    cun
    #
    chash
    cfv
    c1
    cmin
    co
    #
    cfz
    co
    #
    @37
    clt
    clt
    vg
    cv
    #
    wiso
    #
    vg
    cio
    cR
    cS
    cT
    vf
    vz
    vk
    @36
    cF
    cG
    @37
    cL
    @38
    cX
    vw
    fourierdlem115.f
    fourierdlem115.t
    fourierdlem115.per
    fourierdlem115.g
    fourierdlem115.dmdv
    fourierdlem115.dvcn
    fourierdlem115.rlim
    fourierdlem115.llim
    fourierdlem115.x
    fourierdlem115.l
    fourierdlem115.r
    cA
    vn
    cn0
    vx
    @27
    cpi
    cioo
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    @3
    @43
    cmul
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    citg
    #
    cpi
    cdiv
    co
    #
    cmpt
    #
    vk
    cn0
    vx
    @42
    @44
    @14
    @43
    cmul
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    citg
    #
    cpi
    cdiv
    co
    #
    cmpt
    fourierdlem115.a
    vn
    vk
    cn0
    @49
    @55
    @3
    @14
    wceq
    #
    @48
    @54
    cpi
    cdiv
    @56
    vx
    @42
    @47
    @53
    @56
    @47
    @53
    wceq
    @43
    @42
    wcel
    #
    @56
    @46
    @52
    @44
    cmul
    @56
    @45
    @51
    ccos
    @3
    @14
    @43
    cmul
    oveq1
    #
    fveq2d
    oveq2d
    adantr
    itgeq2dv
    oveq1d
    cbvmptv
    eqtri
    cB
    vn
    cn
    vx
    @42
    @44
    @45
    csin
    cfv
    #
    cmul
    co
    #
    citg
    #
    cpi
    cdiv
    co
    #
    cmpt
    #
    vk
    cn
    vx
    @42
    @44
    @51
    csin
    cfv
    #
    cmul
    co
    #
    citg
    #
    cpi
    cdiv
    co
    #
    cmpt
    fourierdlem115.b
    vn
    vk
    cn
    @62
    @67
    @56
    @61
    @66
    cpi
    cdiv
    @56
    vx
    @42
    @60
    @65
    @56
    @60
    @65
    wceq
    @57
    @56
    @59
    @64
    @44
    cmul
    @56
    @45
    @51
    csin
    @58
    fveq2d
    oveq2d
    adantr
    itgeq2dv
    oveq1d
    cbvmptv
    eqtri
    fourierdlem115.s
    @29
    eqid
    vy
    vx
    cr
    @35
    @43
    cpi
    @43
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    @30
    @43
    wceq
    #
    @30
    @43
    @34
    @71
    caddc
    @72
    id
    @72
    @33
    @70
    cT
    cmul
    @72
    @32
    @69
    cfl
    @72
    @31
    @68
    cT
    cdiv
    @30
    @43
    cpi
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    cbvmptv
    @37
    eqid
    @38
    eqid
    @41
    @39
    @37
    clt
    clt
    vf
    cv
    #
    wiso
    vg
    vf
    @39
    @37
    clt
    clt
    @73
    @40
    isoeq1
    cbviotav
    fourierdlem114
    #
    simpld
    wph
    @13
    @24
    @0
    @12
    @23
    @1
    caddc
    cn
    @11
    @22
    vn
    vk
    vk
    @11
    nfcv
    vn
    @18
    @21
    caddc
    vn
    @15
    @17
    cmul
    vn
    @14
    cA
    vn
    cA
    @50
    fourierdlem115.a
    vn
    cn0
    @49
    nfmpt1
    nfcxfr
    vn
    @14
    nfcv
    #
    nffv
    vn
    cmul
    nfcv
    #
    vn
    @17
    nfcv
    nfov
    vn
    caddc
    nfcv
    vn
    @19
    @20
    cmul
    vn
    @14
    cB
    vn
    cB
    @63
    fourierdlem115.b
    vn
    cn
    @62
    nfmpt1
    nfcxfr
    @75
    nffv
    @76
    vn
    @20
    nfcv
    nfov
    nfov
    @56
    @7
    @18
    @10
    @21
    caddc
    @56
    @4
    @15
    @6
    @17
    cmul
    @3
    @14
    cA
    fveq2
    @56
    @5
    @16
    ccos
    @3
    @14
    cX
    cmul
    oveq1
    #
    fveq2d
    oveq12d
    @56
    @8
    @19
    @9
    @20
    cmul
    @3
    @14
    cB
    fveq2
    @56
    @5
    @16
    csin
    @77
    fveq2d
    oveq12d
    oveq12d
    cbvsumi
    oveq2i
    wph
    @2
    @25
    @74
    simprd
    syl5eq
    jca
end
