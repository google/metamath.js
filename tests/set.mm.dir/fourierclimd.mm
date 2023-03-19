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
include "cmpt.mm"
include "nfcv.mm"
include "cn0.mm"
include "cpi.mm"
include "cneg.mm"
include "cioo.mm"
include "citg.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfov.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "fourierdlem115.mm"
include "simpld.mm"

theorem fourierclimd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cL: class L
  let cX: class X
  let vk: setvar k
  assume fourierclimd.f: |- ( ph -> F : RR --> RR )
  assume fourierclimd.t: |- T = ( 2 x. _pi )
  assume fourierclimd.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierclimd.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fourierclimd.dmdv: |- ( ph -> ( ( -u _pi (,) _pi ) \ dom G ) e. Fin )
  assume fourierclimd.dvcn: |- ( ph -> G e. ( dom G -cn-> CC ) )
  assume fourierclimd.rlim: |- ( ( ph /\ x e. ( ( -u _pi [,) _pi ) \ dom G ) ) -> ( ( G |` ( x (,) +oo ) ) limCC x ) =/= (/) )
  assume fourierclimd.llim: |- ( ( ph /\ x e. ( ( -u _pi (,] _pi ) \ dom G ) ) -> ( ( G |` ( -oo (,) x ) ) limCC x ) =/= (/) )
  assume fourierclimd.x: |- ( ph -> X e. RR )
  assume fourierclimd.l: |- ( ph -> L e. ( ( F |` ( -oo (,) X ) ) limCC X ) )
  assume fourierclimd.r: |- ( ph -> R e. ( ( F |` ( X (,) +oo ) ) limCC X ) )
  assume fourierclimd.a: |- A = ( n e. NN0 |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierclimd.b: |- B = ( n e. NN |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierclimd.s: |- S = ( n e. NN |-> ( ( ( A ` n ) x. ( cos ` ( n x. X ) ) ) + ( ( B ` n ) x. ( sin ` ( n x. X ) ) ) ) )

  disjoint F n
  disjoint F x
  disjoint n x
  disjoint G x
  disjoint T x
  disjoint X n
  disjoint X x
  disjoint ph x
  disjoint A k
  disjoint B k
  disjoint F k
  disjoint k n
  disjoint k x
  disjoint G k
  disjoint L k
  disjoint R k
  disjoint T k
  disjoint X k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> seq 1 ( + , S ) ~~> ( ( ( L + R ) / 2 ) - ( ( A ` 0 ) / 2 ) ) )

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
    @1
    cn
    vn
    cv
    #
    cA
    cfv
    #
    @2
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
    @2
    cB
    cfv
    #
    @4
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
    caddc
    co
    @0
    wceq
    wph
    vx
    cA
    cB
    cR
    cS
    cT
    vk
    vn
    cF
    cG
    cL
    cX
    fourierclimd.f
    fourierclimd.t
    fourierclimd.per
    fourierclimd.g
    fourierclimd.dmdv
    fourierclimd.dvcn
    fourierclimd.rlim
    fourierclimd.llim
    fourierclimd.x
    fourierclimd.l
    fourierclimd.r
    fourierclimd.a
    fourierclimd.b
    cS
    vn
    cn
    @10
    cmpt
    vk
    cn
    vk
    cv
    #
    cA
    cfv
    #
    @11
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
    @11
    cB
    cfv
    #
    @13
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    fourierclimd.s
    vn
    vk
    cn
    @10
    @19
    vk
    @10
    nfcv
    vn
    @15
    @18
    caddc
    vn
    @12
    @14
    cmul
    vn
    @11
    cA
    vn
    cA
    vn
    cn0
    vx
    cpi
    cneg
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
    @2
    @21
    cmul
    co
    #
    ccos
    cfv
    cmul
    co
    citg
    cpi
    cdiv
    co
    #
    cmpt
    fourierclimd.a
    vn
    cn0
    @24
    nfmpt1
    nfcxfr
    vn
    @11
    nfcv
    #
    nffv
    vn
    cmul
    nfcv
    #
    vn
    @14
    nfcv
    nfov
    vn
    caddc
    nfcv
    vn
    @16
    @17
    cmul
    vn
    @11
    cB
    vn
    cB
    vn
    cn
    vx
    @20
    @22
    @23
    csin
    cfv
    cmul
    co
    citg
    cpi
    cdiv
    co
    #
    cmpt
    fourierclimd.b
    vn
    cn
    @27
    nfmpt1
    nfcxfr
    @25
    nffv
    @26
    vn
    @17
    nfcv
    nfov
    nfov
    @2
    @11
    wceq
    #
    @6
    @15
    @9
    @18
    caddc
    @28
    @3
    @12
    @5
    @14
    cmul
    @2
    @11
    cA
    fveq2
    @28
    @4
    @13
    ccos
    @2
    @11
    cX
    cmul
    oveq1
    #
    fveq2d
    oveq12d
    @28
    @7
    @16
    @8
    @17
    cmul
    @2
    @11
    cB
    fveq2
    @28
    @4
    @13
    csin
    @29
    fveq2d
    oveq12d
    oveq12d
    cbvmpt
    eqtri
    fourierdlem115
    simpld
end
